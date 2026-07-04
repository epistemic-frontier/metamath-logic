# Predicate Hilbert Module Map

This document records the planned module boundaries for migrating first-order
predicate calculus with equality from `set.mm` into
`logic.predicate.hilbert`.

Engineering guardrails for applying this plan live in
`docs/ENGINEERING_GUARDRAILS.md`.

The main `set.mm` predicate calculus section starts at line 14553 and ends
just before ZF set theory starts at line 24578. Three predicate/equality
syntax declarations are introduced earlier for the `df-tru` construction:
`wal` at line 12017, `cv` at line 12081, and `wceq` at line 12114.

## Current Gap

| Area | Count |
| --- | ---: |
| Main FOL `$p` theorem/lemma targets | 901 |
| Main FOL `$a` syntax/axiom/definition targets | 22 |
| Pre-FOL predicate `$a` targets | 3 |

Current implementation status:

- `logic.predicate.hilbert` owns basic tokens for `A.`, `E.`, `=`, and `e.`.
- It has author-facing constructors for `All`, `Exists`, `Eq`, and `Elem`.
- It has placeholder axiom schemas `AX5` through `AX13`.
- It does not yet emit predicate assertions in `logic.build`.
- It does not yet have a predicate theorem registry.
- It does not yet model `setvar`, `class`, `wff`, and `$d` constraints with
  enough fidelity for set.mm proof migration.

## Package Layout

```text
logic/predicate/hilbert/
  _builtins.py
  _structures.py
  system.py
  syntax.py
  quantifiers.py
  not_free.py
  equality.py
  substitution.py
  membership.py
  core_schemes.py
  uniqueness.py
  theorems.py
  axiomatizations/
    __init__.py
    aristotle.py
    intuitionistic.py
```

## Section Map

| set.mm section | Range | `$p` | `$a` | Target module |
| --- | ---: | ---: | ---: | --- |
| Pre-FOL dependencies for `df-tru` | 11990-12114 | 0 | 3 | `syntax.py` |
| Universal quantifier continued; `exists` and not-free | 14626-14811 | 12 | 4 | `syntax.py`, `quantifiers.py`, `not_free.py` |
| `ax-gen`, `ax-4`, quantifier basics | 14812-15649 | 109 | 2 | `quantifiers.py` |
| Empty domain of discourse note | 15650-15686 | 4 | 0 | `quantifiers.py` |
| `ax-5` distinctness | 15687-16214 | 51 | 1 | `quantifiers.py`, `not_free.py` |
| Equality predicate continued | 16215-16283 | 5 | 0 | `equality.py` |
| `ax-6` existence | 16284-16699 | 40 | 1 | `equality.py` |
| `ax-7` equality | 16700-17349 | 56 | 1 | `equality.py` |
| Proper substitution | 17350-17847 | 43 | 2 | `substitution.py` |
| Membership predicate | 17848-17914 | 1 | 1 | `membership.py` |
| `ax-8` membership left equality | 17915-18018 | 7 | 1 | `membership.py` |
| `ax-9` membership right equality | 18019-18124 | 9 | 1 | `membership.py` |
| Redundancy of `ax-10`..`ax-13` | 18125-18375 | 13 | 0 | `core_schemes.py` |
| Auxiliary axiom schemes | 18376-22473 | 383 | 4 | `core_schemes.py`, `substitution.py` |
| Uniqueness and unique existence | 22474-23854 | 123 | 4 | `uniqueness.py` |
| Other predicate axiomatizations | 23855-24449 | 30 | 0 | `axiomatizations/aristotle.py` |
| Intuitionistic logic aliases | 24450-24577 | 15 | 0 | `axiomatizations/intuitionistic.py` |

## Registry Pattern

Each module should own a local `THEOREMS` mapping from set.mm labels to proof
constructor functions. The aggregate registry should live in
`logic.predicate.hilbert.theorems`.

```python
from .quantifiers import THEOREMS as QUANTIFIERS
from .equality import THEOREMS as EQUALITY

SETMM_TO_PREDICATE_THEOREMS = {
    **QUANTIFIERS,
    **EQUALITY,
}
```

The existing `SETMM_TO_PREDICATE_AXIOMS` should remain separate from theorem
constructors, but it needs to include `ax-gen` and `ax-4` once those schemas
are represented correctly.

## Migration Order

1. Build the syntax and type layer.
   Represent `setvar`, `class`, predicate-owned wff constructors, and `$d`
   constraints explicitly enough for set.mm alignment.

2. Emit predicate assertions.
   Wire predicate syntax and axiom schemas into `logic.build`, starting with
   `wal`, `wex`, `wnf`, `weq`, `wel`, `ax-gen`, and `ax-4` through `ax-9`.

3. Add the theorem registry.
   Introduce module-local `THEOREMS` maps and aggregate them in
   `theorems.py`.

4. Migrate quantifier and not-free hubs.
   These are the main dependency base for the rest of FOL.

5. Migrate equality and membership.
   These are required before set-theory packages can depend on predicate
   logic with useful fidelity.

6. Migrate proper substitution and auxiliary schemes.
   This includes `df-sb` and the large `ax-10` through `ax-13` closure.

7. Migrate uniqueness and alternative axiomatizations last.
   These sections are important but should not block the FOL-to-ZF bridge.

## Boundary Notes

- The predicate package should own `wal`, `cv`, and `wceq` even though set.mm
  introduces them before the main predicate section.
- `cv` is class syntax, so predicate migration must coordinate with the later
  set-theory/class layer. For this package, keep only the minimal class syntax
  needed for equality and `df-tru`.
- `e.` is introduced as the membership predicate in predicate logic, while set
  theory later gives it mathematical content through ZF axioms.
- Alternative predicate axiomatizations are derivability results inside the
  standard predicate Hilbert environment, not independent proof kernels for
  the first migration pass.
