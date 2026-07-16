# metamath-logic Module Plan and Current Status

This document originally tracked migration from the set.mm logic range into
Python. The migration phases below are retained as historical context; the
authoritative current status is stated first so the old plan is not mistaken
for unfinished work.

## Current status

The implementation is split into `logic.prop` and
`logic.fol`. Their registries contain 1,764 and 911 proofs,
respectively (2,675 total).

The source closure audit reports 2,675 unique `prove_*` identities, all in the
registries, with 0 support-only and 0 uncovered. Latest verification reports
2,675 declared, 5,004 emitted, and 213 declared-but-unemitted proofs.
`mmverify`, `metamath`, and `knife` pass.

Both scopes now use the same public API architecture:

```text
logic/{prop,fol}/
  __init__.py       # public facade
  axioms.py         # AXIOMS
  rules.py          # RULES
  theorems.py       # THEOREMS
  <topic>.py        # public prove_* functions
  _system.py        # internal System implementation
  _*.py             # internal structures and mechanics
```

The three category modules form the metadata API used by the builder. Public
topic modules remain the direct, low-friction API for importing individual
`prove_*` constructors. Axiom labels use canonical set.mm spelling `ax-1`
through `ax-13`; names such as `A1` and `AX5` are only Python implementation
identifiers.

## Historical migration plan

The original plan grouped work into propositional core, implication,
remaining connectives, then predicate calculus (lines 14721–24944 in the
current local set.mm snapshot). It also
proposed finer predicate files such as `quantifiers.py`, `not_free.py`, and
`equality.py`. Those were planning boundaries, not the final architecture;
their implemented mathematical content now resides in predicate `axioms.py`,
`lemmas.py`, and `theorems.py`.

Similarly, earlier references to skeleton modules, connective-lowering
blockers, `pm2.07` being registered-only, placeholder predicate axioms, and an
unemitted predicate registry described intermediate states and are now
superseded. The current build has full registry emission, including `dfifp4`.
The duplicate package-local modus-tollens constructor was removed in favor of
the canonical set.mm theorem `mto`.

## Verification

```bash
uv run --no-sync skfd verify --level 1 metamath-logic
```

The catalogue is a derived release artifact, not part of each theorem change.
Regenerate it once during release preparation with
`uv run --no-sync python tools/generate_lemma_catalogue.py`, then validate it
with the same command plus `--check`.
