# metamath-logic

This is the Project 025 V2 public proof-source release for
`logic`.

- Python root: `logic`
- Version: `0.0.11`
- Governed modules: 26
- Public proof functions: 2758
- Runtime provider: `metamath-setmm-provider==0.1.0`
- Proof authoring runtime: `proof-scaffold==0.0.13`

Assertion handles and formations are owned by the private provider. Proof
functions are owned by the public taxonomy modules in this repository.
Direct proof dependencies resolve provider handles inside each proof
function; this package has no runtime dependency on another public package.

## Development

```console
uv sync --dev
uv run ruff check .
uv run python -m pytest
```
