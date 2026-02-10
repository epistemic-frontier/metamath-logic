# metamath-logic Authoring Style Guide (Draft)

This document defines the authoring conventions for `metamath-logic`.
It is aligned with the ProofScaffold **BuilderV2 v1 frozen contract** and the migration plan:

- BuilderV2 invariants: [009_builder-v2.md](file:///Users/mingli/MetaMath/proof-scaffold/references/009_builder-v2.md)
- Motivation / friction points: [017-builder_v2.md](file:///Users/mingli/MetaMath/proof-scaffold/projects/017-builder_v2.md)
- Migration slices / acceptance: [018-builder-v2-migration.md](file:///Users/mingli/MetaMath/proof-scaffold/projects/018-builder-v2-migration.md)

The goal is to keep author code “math-first” while ensuring the toolchain can deterministically build, link, and verify artifacts.

## 0. Non-Negotiable Invariants

These are the rules we optimize everything else around:

1. **Single build entrypoint**: packages expose `build(ctx)` only.
2. **SymbolId-only across package boundaries**: cross-package interaction is `SymbolId` only, not raw string tokens.
3. **ASCII canonical artifacts**: IR and emitted `.mm` are ASCII-only and deterministic.
4. **Unicode is authoring-only**: Unicode may appear in authoring surfaces, but must enter the canonical world only through `NameResolver/Lexicon`, producing machine-readable mapping artifacts.
5. **Auto-$f by default**: authors do not hand-write repetitive `$v/$f`.

## 1. Layer Model (Where Things Belong)

Authoring stays clean only if responsibilities do not leak.

### 1.1 Authoring Layer (Expr)

Files in this layer must only build **Expr trees**:

- formal variables (φ, ψ, χ, …)
- constructors/connectives (→, ¬, ∧, …)
- axiom schemas and definitions as Expr
- lemma “proof scripts” as structured steps (still author-facing)

Authoring code must not:

- depend on toolchain globals
- read builder private fields
- manufacture temporary token names
- perform verification

### 1.2 Compilation Bridge (Expr → Wff tokens)

There is exactly one place where Expr turns into token-level formulas (`Wff.tokens`):

- it must use the global interner (`ctx.mm.interner`)
- it must go through the canonicalization policy (`ctx.names`)

The bridge is allowed to fail fast with a typed, local error message.

### 1.3 Emission Layer (IR via MMBuilderV2)

Emission consumes `SymbolId` sequences and produces IR via `MMBuilderV2` only:

- no string token DSL for proof/expr payloads
- auto-$f handles floating hypotheses
- `mm.export(...)` is the only export mechanism

## 2. Directory / File Responsibilities (Hilbert Example)

Use strict separation. Each file should have one responsibility:

```
logic/propositional/hilbert/
  _structures.py     # Language skeleton: Vars + constructors only
  axioms.py          # Axiom schemas (Expr only)
  _syntactic.py      # Token-level rule skeleton (mp/wi/wn/wa) if needed
  lemmas/*.py        # Lemma proof scripts (author-facing)
  theorems.py        # set.mm label → local lemma constructor registry
  __init__.py        # HilbertSystem facade (author_env/compile/apply)
```

Current code references:

- Language skeleton: [hilbert/_structures.py](file:///Users/mingli/MetaMath/metamath-logic/src/logic/propositional/hilbert/_structures.py)
- Axioms: [hilbert/axioms.py](file:///Users/mingli/MetaMath/metamath-logic/src/logic/propositional/hilbert/axioms.py)
- Lemmas (current, to be split): [hilbert/lemmas.py](file:///Users/mingli/MetaMath/metamath-logic/src/logic/propositional/hilbert/lemmas.py)
- Registry: [hilbert/theorems.py](file:///Users/mingli/MetaMath/metamath-logic/src/logic/propositional/hilbert/theorems.py)

## 3. Naming Conventions

### 3.1 Package identity: dist name vs module name

- **Toolchain identity** is the dist/project name from `pyproject.toml` (e.g. `metamath-logic`).
- **Python import name** is the module name (e.g. `logic`).
- Author code should access dependencies through `ctx.deps`, never via kwargs injection.

### 3.2 Labels

- Use set.mm labels verbatim when the statement corresponds 1:1 with set.mm (e.g. `pm2.24`).
- For any lemma that is not a set.mm label, require an explicit namespace prefix (e.g. `HILBERT_L1_id`).
- Never rely on “pretty Unicode labels” for emitted artifacts; they will be canonicalized.
-
- Export policy:
  - set.mm-aligned labels may be exported as API surface.
  - non-set.mm labels are internal by default; exporting them requires an explicit rationale in `build.py`.

### 3.3 Files and functions

- For a set.mm theorem `pm2.24`, the preferred local constructor is `prove_pm2_24`.
- Keep a single registry mapping in [theorems.py](file:///Users/mingli/MetaMath/metamath-logic/src/logic/propositional/hilbert/theorems.py).
- Keep the public catalogue in [LEMMA_CATALOGUE.md](file:///Users/mingli/MetaMath/metamath-logic/LEMMA_CATALOGUE.md) in sync.

## 4. Authoring DSL Rules (Expr)

### 4.1 Prefer constructors; allow parser as a convenience

We allow both:

1. **Constructor-based Expr**, for stable, refactorable authoring.
2. **`wff("...")` parsing**, as a convenience for quick scripts and test fixtures.

Rule:

- If a formula is “core API surface” (axioms, key definitions), prefer constructor-based Expr.
- If a formula is “proof script glue” and readability improves, parser strings are acceptable.
-
- Unicode style requirement:
  - Parser strings must be written in Unicode authoring style (e.g. `φ`, `ψ`, `→`, `¬`, `∧`), not legacy ASCII shorthands like `ph/ps/->/-.`.

### 4.2 Keep the symbol set minimal and explicit

Constructors must be declared once in the language skeleton and exported.
Do not re-declare the same connective in multiple modules.

## 5. Proof Script Contract (Lemmas)

### 5.1 Default to “lowerable” steps

The default lemma representation should be lowerable into a real Metamath proof (SymbolId tokens),
using the lowered emitter path.

Target step kinds:

- `hyp`: local hypothesis
- `ref`: reference to an axiom/theorem label
- `mp`: modus ponens, explicitly referencing two prior steps

This is aligned with the lowered emission support in:
[emit_lowered_lemmas](file:///Users/mingli/MetaMath/proof-scaffold/src/skfd/authoring/emit.py#L93-L270)

Hard requirement:

- Every entry listed in [LEMMA_CATALOGUE.md](file:///Users/mingli/MetaMath/metamath-logic/LEMMA_CATALOGUE.md) must be lowerable.

### 5.2 Separate semantics from commentary

Do not encode proof semantics in free-form text.

Bad pattern:

- using a single `step(...)` API and “guessing” a referenced label from the first token of a note

Good pattern:

- `lb.ref(..., ref="A1", note="...")` makes the dependency explicit
- `note="A1 with (phi, psi) = (φ, ¬ψ)"` is commentary only

### 5.3 Stub policy (allowed, but explicit)

Stub lemmas are allowed only for experimental work that is not part of the public catalogue.

- A lemma listed in [LEMMA_CATALOGUE.md](file:///Users/mingli/MetaMath/metamath-logic/LEMMA_CATALOGUE.md) must not be stubbed.
- If a lemma is stubbed, it must not be exported.

## 6. build.py Style (Orchestration Only)

`build(ctx)` should:

- construct the system with the global interner
- import required typecodes from deps (`wff = ctx.deps.prelude["wff"]`)
- emit axioms, rule skeleton, lemmas in a deterministic order
- export a fixed list of labels

It should not:

- perform canonicalization itself
- construct temporary token maps
- access any private fields of `mm`
- bake dependency naming policy (dist vs module) into author code

See: [logic/build.py](file:///Users/mingli/MetaMath/metamath-logic/src/logic/build.py)

## 7. Unicode / Canonicalization Rules

### 7.1 What authors may write

- Unicode variables and connectives are allowed in authoring surfaces.
- Display choices should be ergonomic for humans.

### 7.2 What artifacts must contain

- IR and `.mm` are ASCII canonical only.
- Any Unicode used during authoring must be recorded via the `NameResolver` mapping artifact (`*.names.json`).

Practical rule:

- If you create any new Unicode alias, update the lexicon policy (toolchain-side), not ad-hoc in a proof script.

## 8. Determinism Rules

To preserve deterministic builds:

- do not iterate over plain `set`/`dict` unless the order is explicitly sorted
- keep emission order stable and documented (axioms → skeleton → lemmas → theorems)
- keep registry iteration stable (explicit ordered list, not `globals()` unless `export_axioms` guarantees ordering semantics you want)

## 9. Verification Workflow (Expected)

The expected “green path” for this repository:

- `proof-scaffold`: `uv run pytest`
- `metamath-logic`: `uv run python -m skfd.cli verify metamath-logic`

Note: `verify` targets the dist/project name from `pyproject.toml`, not the module name.

## 10. Open Decisions (Discuss)

1. **Rule surface**: do we keep `_syntactic.py` as token-level truth for `mp/wi/wn/wa`, or migrate it into a unified authoring symbol table?
