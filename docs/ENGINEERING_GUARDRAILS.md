# Engineering Guardrails for set.mm Migration

These guardrails keep the `metamath-logic` migration incremental, verifiable,
and safe to review. They apply to the propositional and predicate Hilbert
module plans.

## Source of Truth

- `set.mm/set.mm` labels are the canonical external labels.
- Module maps document ownership only; they do not imply a theorem is migrated.
- A theorem counts as migrated only when its constructor is registered and the
  build emits it into a verifier-checked artifact.
- A syntax/axiom/definition counts as migrated only when `build(ctx)` emits the
  matching Metamath assertion with the set.mm label or an explicitly documented
  package-local label.

## Package Boundaries

- `metamath-prelude` owns only the foundation frame and stable base tokens.
- `logic.propositional.hilbert` owns propositional connectives, Hilbert proof
  constructors, and alternative propositional axiomatization derivations.
- `logic.predicate.hilbert` owns `setvar`, quantifiers, equality and membership
  predicates, not-free reasoning, substitution, and predicate axiom schemes.
- Set-theory packages may depend on predicate syntax and theorems, but predicate
  migration must not depend on ZF-specific axioms.
- Alternative axiomatizations start as derivability results inside the current
  Hilbert packages. Do not create independent proof kernels until there is a
  concrete need for separately runnable systems.

## Registry Guardrails

- Each theorem-owning module exposes a local `THEOREMS` mapping.
- Aggregate registries live in `theorems.py` for the package:
  - `SETMM_TO_HILBERT_LEMMAS`
  - future `SETMM_TO_PREDICATE_THEOREMS`
- Registry keys must be exact set.mm labels.
- A constructor registered under label `L` must produce proof name `L`.
- Do not register a theorem until its constructor can be validated locally.
- Registered-but-not-emitted entries must be explicit and documented, with the
  blocking reason recorded in catalogue output or roadmap text.
- Registry aggregation order must be deterministic. Prefer explicit module maps
  over `globals()` collection.

## Build and Emission Guardrails

- Skeleton modules may import cleanly and expose empty registries, but they must
  not change `build(ctx)` behavior.
- A module may be connected to `build(ctx)` only after:
  - its syntax constructors lower to the intended token sequence,
  - its direct dependencies are emitted or dependency-provided,
  - unresolved references fail fast during build.
- Keep authoring registry size and emitted proof surface distinct:
  - authoring registry can lead,
  - emitted coverage must state what was dropped and why.
- If a theorem depends on a connective outside the current lowering subset, keep
  it registered-only or unregistered until the lowering path exists.

## Predicate-Specific Guardrails

- `wal`, `cv`, and `wceq` are predicate/equality-owned even though set.mm
  introduces them before the main predicate section.
- Predicate syntax must eventually distinguish `setvar`, `class`, and `wff`.
  Do not encode long-term predicate semantics as generic `WFF` placeholders.
- `$d` side conditions must be represented before migrating proofs that rely on
  distinct-variable constraints.
- `df-tru` may use a short-term propositional abstraction for `T.`, but the
  faithful bridge to `wal`, `cv`, and `wceq` must remain documented.
- `e.` is predicate syntax; ZF set theory gives it mathematical content later.

## Verification Gates

Run the smallest useful gate for the change, and document anything skipped.

For documentation-only changes:

```bash
uv run ruff check docs/MODULE_PLAN.md docs/PROPOSITIONAL_HILBERT_MODULES.md docs/PREDICATE_HILBERT_MODULES.md docs/ENGINEERING_GUARDRAILS.md
```

For skeleton or import-only Python changes:

```bash
python3 -m compileall -q src/logic/propositional src/logic/predicate
uv run ruff check src/logic/propositional src/logic/predicate docs
uv run python -c 'from logic.propositional.hilbert import axiomatizations'
uv run python -c 'from logic.predicate.hilbert import PredicateSystem'
```

For theorem registry changes:

```bash
uv run ruff check .
uv run mypy .
uv run python -m pytest
uv run python tools/generate_lemma_catalogue.py
uv run skfd verify --coverage declared --level 1 metamath-logic
```

`--coverage declared` is allowed to fail only when the failure is the expected
declared-vs-emitted gap and the final report states the gap explicitly.

## Counting and Roadmap Guardrails

- When adding a new migration slice, record:
  - set.mm line range,
  - `$p` target count,
  - `$a` target count,
  - target module,
  - current blocker.
- Update `MODULE_PLAN.md` whenever the migration status, target module, or
  priority changes.
- Update the relevant module map when ownership boundaries move.
- Regenerate `LEMMA_CATALOGUE.md` whenever the Hilbert theorem registry or
  current lowering filter changes.

## Definition of Done

A migrated slice is done only when:

- syntax and theorem labels align with set.mm or documented aliases,
- constructors validate against the local proof registry,
- emitted artifacts verify with the configured Metamath verifier,
- dependency closure is explicit,
- module ownership is documented,
- roadmap counts and status are updated,
- tests cover the new public surface or the residual risk is stated.
