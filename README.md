# metamath-logic

`metamath-logic` is a small Python package that exports the “logic” layer used by ProofScaffold-based Metamath projects.
It provides reusable propositional and predicate logic artifacts that downstream packages can depend on and link against.

## Versioning

- Package version: `0.0.6`
- ProofScaffold dependency: `proof-scaffold==0.0.9`
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
- Complete propositional and predicate theorem registries: 1,684 declared
  proofs, all emitted into the verifier-checked build.
- Propositional syntax/helpers beyond the foundation frame: `wa`, `wo`, `wb`,
  `wtru`, `wfal`, `mp`, `idi`, `a1ii`.
- A migration guide for the logic layer refactor.

## Migration guide

- [`docs/LOGIC_MIGRATION_GUIDE.md`](docs/LOGIC_MIGRATION_GUIDE.md)

## Verification

This repository uses `uv` for reproducible installs and runs `skfd verify --level 1` as the primary correctness gate.

From this repository directory:

```bash
uv sync --locked --dev
uv run --frozen ruff check .
uv run --frozen mypy .
uv run --frozen python -m pytest
uv run --frozen skfd verify --level 1 metamath-logic
```

`skfd verify` builds the package into a verification monolith (under `target/`) and checks it with the configured verifiers.

For a concise verification of the current checkout, run:

```bash
uv run --no-sync skfd verify --level 1 metamath-logic
```

Latest result: 1,684 declared proofs, 3,610 emitted proofs, and 0
declared-but-unemitted; `mmverify`, `metamath`, and `knife` all pass.
