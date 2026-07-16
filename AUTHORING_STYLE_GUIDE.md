# metamath-logic Authoring Style Guide

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
  implication.py     # Proof scripts, by category (see placement rule below)
  negation.py
  disjunction.py
  conjunction.py
  equivalence.py
  constants.py
  syllogism.py       # frozen legacy subdivision of implication (see below)
  lemmas.py          # pure re-export shim (NO proof defs)
  theorems.py        # explicit set.mm label → constructor registry
  __init__.py        # System facade (author_env/compile/apply)
```

The predicate facade is `logic/predicate/hilbert/__init__.py` and exposes
`PredicateSystem`. Predicate internals are `_builtins.py`, `_structures.py`,
and `_internal.py`; public mathematical content is in `axioms.py`, `lemmas.py`,
and `theorems.py`. There is no predicate `system.py` or `definitions.py`.

### Proof placement rule (where a `prove_*` lives)

- **Every `prove_*` is defined in exactly one category file.** Never define the
  same proof in two modules.
- **Choose the category file from the set.mm *section* the label lives in**,
  which set.mm keys off the *last-introduced connective in the statement* (not
  the proof). Inference/deduction variants (`*i`, `*d`, `*dd`, `*ii`) live with
  their closed form.

  | set.mm section | file |
  |---|---|
  | Logical implication (pure `→`) | `implication.py` |
  | Logical negation (`¬`) | `negation.py` |
  | Logical equivalence (`↔`) | `equivalence.py` |
  | Logical disjunction (`∨`) | `disjunction.py` |
  | Logical conjunction (`∧`) | `conjunction.py` |
  | True/false constants (`⊤`/`⊥`) | `constants.py` |
  | Stoic / mixed connectives | `stoic.py` |

- `syllogism.py` has **no** set.mm counterpart (`syl*`/`com*` are all in the
  "Logical implication" section). Treat it as a frozen legacy bucket: leave its
  existing contents, but **place new proofs by the rule above** — nothing new
  goes into `syllogism.py`.
- Category files must **not** import from one another; proof steps reference
  lemmas by string (`ref="pm2.18"`), so placement never creates import edges.
- Known legacy misplacements exist (e.g. `notnot`/`notnotr`/`pm2_18` in
  `implication.py`, `pm2_01`/`pm2_43` in `syllogism.py`). Do not mass-relocate
  them (pure churn); apply the rule to new and moved code.
- `lemmas.py` and `theorems.py` contain no propositional `def prove_*`.
  `lemmas.py` re-exports the full constructor surface (imports from category
  files + `__all__`); `theorems.py` explicitly defines the
  `SETMM_TO_HILBERT_LEMMAS` label-to-constructor registry.

Current code references:

- Language structures: [`hilbert/_structures.py`](src/logic/propositional/hilbert/_structures.py)
- Axioms: [`hilbert/axioms.py`](src/logic/propositional/hilbert/axioms.py)
- Proof scripts by category: [`hilbert/implication.py`](src/logic/propositional/hilbert/implication.py), [`negation.py`](src/logic/propositional/hilbert/negation.py), [`disjunction.py`](src/logic/propositional/hilbert/disjunction.py), [`constants.py`](src/logic/propositional/hilbert/constants.py)
- Re-export surface: [`hilbert/lemmas.py`](src/logic/propositional/hilbert/lemmas.py)
- Registry: [`hilbert/theorems.py`](src/logic/propositional/hilbert/theorems.py)

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
  - non-set.mm labels are internal by default; exporting them requires an explicit rationale in `_build.py`.

### 3.3 Files and functions

- For a set.mm theorem `pm2.24`, the preferred local constructor is `prove_pm2_24`.
- Register new constructors in `MIGRATION_THEOREMS` at the end of their owning
  category module. [`theorems.py`](src/logic/propositional/hilbert/theorems.py)
  composes those local mappings with the legacy registry.
- [`lemmas.py`](src/logic/propositional/hilbert/lemmas.py) is a frozen
  compatibility shim; routine migrations must not extend it. New theorem
  transactions therefore touch only their owning category module.
- [`LEMMA_CATALOGUE.md`](LEMMA_CATALOGUE.md) is a release artifact generated from
  both registries and the build emission surface. Routine proof migrations must
  not edit it. Release preparation runs
  `uv run --no-sync python tools/generate_lemma_catalogue.py`; strict validation
  uses the same command with `--check`.

## 4. Authoring DSL Rules (Expr)

### 4.1 Prefer constructors; allow parser as a convenience

We allow both:

1. **Constructor-based Expr**, for stable, refactorable authoring.
2. **`wff("...")` parsing**, as a convenience for quick scripts and test fixtures.

Rule:

- If a formula is “core API surface” (axioms, key definitions), prefer constructor-based Expr.
- If a formula is “proof script glue” and readability improves, parser strings are acceptable.
- Parser string style:
  - Unicode authoring style (e.g. `φ`, `ψ`, `→`, `¬`, `∧`) is preferred for new examples and public-facing proof scripts.
  - ASCII/set.mm shorthands such as `ph`, `ps`, `->`, and `-.` remain supported and are common in current migration code and tests.
  - Emitted IR and `.mm` are always ASCII canonical after name resolution.

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

Hard requirements:

- Every catalogue row with status `lowered/exported` must be lowerable and verifier-backed.
- Every registered catalogue proof must be emitted by `_build.py` and verifier-backed.

### 5.2 Separate semantics from commentary

Do not encode proof semantics in free-form text.

Bad pattern:

- using a single `step(...)` API and “guessing” a referenced label from the first token of a note

Good pattern:

- `lb.ref(..., ref="ax-1", note="...")` makes the dependency explicit
- `note="ax-1 with (phi, psi) = (φ, ¬ψ)"` is commentary only

### 5.3 Stub policy (allowed, but explicit)

Stub lemmas are allowed only for experimental work that is not part of the public catalogue.

- A lemma listed in [`LEMMA_CATALOGUE.md`](LEMMA_CATALOGUE.md) must not be stubbed.
- If a lemma is stubbed, it must not be exported.

## 6. _build.py Style (Orchestration Only)

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

See: [`logic/_build.py`](src/logic/_build.py)

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

- `proof-scaffold`: `uv run --no-sync pytest`
- `metamath-logic`: `uv run --no-sync skfd verify --level 1 metamath-logic`

The latest run reports 1,684 declared, 3,610 emitted, and 0
declared-but-unemitted proofs; all three configured verifiers pass.

Note: `verify` targets the dist/project name from `pyproject.toml`, not the module name.

## 10. Open Decisions (Discuss)

1. **Rule surface**: do we keep `_syntactic.py` as token-level truth for `mp/wi/wn/wa`, or migrate it into a unified authoring symbol table?
