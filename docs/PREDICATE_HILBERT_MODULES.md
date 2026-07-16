# Predicate Hilbert Modules

This is the current module map for first-order predicate calculus with equality
in `logic.fol`. The package owns quantifiers, equality,
membership, not-free reasoning, substitution, and predicate axiom schemes.

## Architecture

```text
logic/fol/
  __init__.py       # public facade
  axioms.py         # public AXIOMS registry
  rules.py          # public RULES registry
  theorems.py       # public THEOREMS registry
  _system.py        # internal first-order System implementation
  _builtins.py      # interned predicate tokens
  _structures.py    # Expr variables and constructors
  _internal.py      # compilation/application implementation
  foundation.py     # public foundational prove_* functions
  *.py              # other public theorem topic modules
```

Consumers import `System` from the package facade. `AX5` through
`AX13` are Python-safe Expr constant identifiers only; proof and emitted
assertion labels are the canonical set.mm names `ax-5` through `ax-13` (and
likewise for `ax-4`).

## Current status

- `THEOREMS` contains 911 proofs.
- Predicate syntax and axioms are integrated into `logic.build`.
- Predicate theorem constructors live in public topic modules and remain
  directly importable; `theorems.py` deterministically merges their private
  metadata registries and rejects duplicate labels.
- Together with 1,764 propositional registry proofs, the build declares 2,675
  registry proofs.

The complete source audit finds 2,675 unique `prove_*` constructors, all in the
registries, with 0 support-only and 0 uncovered. Latest verification reports
5,004 emitted and 213 declared-but-unemitted proofs; `mmverify`, `metamath`, and
`knife` all pass.

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
