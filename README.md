# metamath-logic

`metamath-logic` is a small Python package that exports the “logic” layer used by ProofScaffold-based Metamath projects.
It provides reusable propositional and predicate logic artifacts that downstream packages can depend on and link against.

## Versioning

- Package version: `0.0.2`
- ProofScaffold dependency: `proof-scaffold==0.0.5`
- Prelude dependency: `metamath-prelude==0.0.2`

## Installation

This package is published on PyPI: https://pypi.org/project/metamath-logic/

With `uv`:

```bash
uv add metamath-logic
```

## What this package contains

- A ProofScaffold `build.py` entrypoint that emits the logic layer as a linkable unit.
- Authoring-facing propositional and predicate logic libraries (Hilbert-style systems).
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

