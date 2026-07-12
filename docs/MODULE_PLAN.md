# metamath-logic Module Plan and Current Status

This document originally tracked migration from the set.mm logic range into
Python. The migration phases below are retained as historical context; the
authoritative current status is stated first so the old plan is not mistaken
for unfinished work.

## Current status

The implementation is split into `logic.propositional.hilbert` and
`logic.predicate.hilbert`. Their registries contain 1,353 and 331 proofs,
respectively (1,684 total), and the complete registry is emitted.

The source closure audit reports 1,734 unique `prove_*` identities: 1,684
registry identities plus 50 support-only identities, with 0 uncovered. Latest
verification reports 1,684 declared, 3,610 emitted, and 0
declared-but-unemitted proofs. `mmverify`, `metamath`, and `knife` pass.

Propositional mathematical content is divided by connective among
`implication.py`, `negation.py`, `equivalence.py`, `conjunction.py`,
`disjunction.py`, `constants.py`, `truth_tables.py`, `adder.py`, `stoic.py`,
and `axiomatizations/`; `theorems.py` is the aggregate registry.

Predicate architecture is intentionally compact:

```text
logic/predicate/hilbert/
  __init__.py       # public PredicateSystem facade
  _builtins.py      # internal tokens
  _structures.py    # internal Expr structures
  _internal.py      # internal processing
  axioms.py         # public axiom schemas
  lemmas.py         # public proof constructors
  theorems.py       # public registry
```

There is no predicate `system.py` or `definitions.py`. Axiom proof labels use
canonical set.mm spelling `ax-1` through `ax-13`; names such as `A1` and `AX5`
are only Python-safe Expr identifiers.

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
