# Predicate Hilbert Modules

This is the current module map for first-order predicate calculus with equality
in `logic.predicate.hilbert`. The package owns quantifiers, equality,
membership, not-free reasoning, substitution, and predicate axiom schemes.

## Architecture

```text
logic/predicate/hilbert/
  __init__.py       # public PredicateSystem facade and axiom-label map
  _builtins.py      # interned predicate tokens
  _structures.py    # Expr variables and constructors
  _internal.py      # compilation/application implementation
  axioms.py         # ax-4 through ax-13 Expr schemas
  lemmas.py         # predicate prove_* constructors
  theorems.py       # SETMM_TO_PREDICATE_THEOREMS registry
```

`system.py` and predicate `definitions.py` no longer exist. Consumers import
`PredicateSystem` from the package facade. `AX5` through `AX13` are Python-safe
Expr constant identifiers only; proof and emitted assertion labels are the
canonical set.mm names `ax-5` through `ax-13` (and likewise for `ax-4`).

## Current status

- `SETMM_TO_PREDICATE_THEOREMS` contains 331 proofs.
- Predicate syntax and axioms are integrated into `logic.build`.
- Every predicate registry proof is emitted; none is registered-only.
- Predicate theorem constructors live in `lemmas.py`, and the catalogue links
  there directly.
- Together with 1,353 propositional registry proofs, the build declares all
  1,684 registry proofs.

The complete source audit finds 1,734 unique `prove_*` constructors: 1,684
registry constructors and 50 support-only constructors, with 0 uncovered.
Latest verification emitted 3,610 proofs with 0 declared-but-unemitted;
`mmverify`, `metamath`, and `knife` all pass.

## Boundaries

- The predicate package owns `wal`, `cv`, and `wceq`, although set.mm first
  introduces them before its main predicate section for `df-tru`.
- `e.` is predicate syntax here; later set-theory axioms supply its set-theoretic
  content.
- Alternative predicate axiomatizations remain derivability results in the
  standard Hilbert environment, not separate proof kernels.

Verify the integrated package with:

```bash
uv run --no-sync skfd verify --level 1 metamath-logic
```
