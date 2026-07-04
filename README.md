# metamath-logic

`metamath-logic` is a small Python package that exports the “logic” layer used by ProofScaffold-based Metamath projects.
It provides reusable propositional and predicate logic artifacts that downstream packages can depend on and link against.

## Versioning

- Package version: `0.0.5`
- ProofScaffold dependency: `proof-scaffold==0.0.8`
- Prelude dependency: `metamath-prelude==0.0.5`

## Installation

This package is published on PyPI: https://pypi.org/project/metamath-logic/

With `uv`:

```bash
uv add metamath-logic
```

## What this package contains

- A ProofScaffold `build.py` entrypoint that emits the logic layer as a linkable unit.
- Authoring-facing propositional and predicate logic libraries (Hilbert-style systems).
- Propositional syntax/helpers beyond the foundation frame: `wa`, `wo`, `wb`,
  `wtru`, `wfal`, `mp`, `idi`, `a1ii`.
- A migration guide for the logic layer refactor.

## Migration guide

- [`docs/LOGIC_MIGRATION_GUIDE.md`](docs/LOGIC_MIGRATION_GUIDE.md)

## Verification

This repository uses `uv` for reproducible installs and runs `skfd verify --level 1` as the primary correctness gate.

From the `metamath-logic/` directory:

```bash
uv sync --locked --dev
uv run --frozen ruff check .
uv run --frozen mypy .
uv run --frozen python -m pytest
uv run --frozen skfd verify --level 1 metamath-logic
```

`skfd verify` builds the package into a verification monolith (under `target/`) and checks it with the configured verifiers.

When using a ProofScaffold version that supports proof coverage declarations,
the package declares its Hilbert theorem registry during `build(ctx)`. To require
that every declared theorem is emitted into the verification monolith, run:

```bash
uv run --frozen skfd verify --coverage declared --level 1 metamath-logic
```

This is stricter than artifact verification and is expected to fail until the
declared registry and emitted proof closure are aligned.
