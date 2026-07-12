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

- Proof constructors have one owning module. Propositional `lemmas.py`
  re-exports its category constructors; predicate constructors live directly
  in predicate `lemmas.py`.
- The single authoritative registry for each package lives in `theorems.py`:
  - `SETMM_TO_HILBERT_LEMMAS`
  - `SETMM_TO_PREDICATE_THEOREMS`
- Registry keys must be exact set.mm labels.
- A constructor registered under label `L` must produce proof name `L`.
- Do not register a theorem until its constructor can be validated locally.
- Registered entries must be emitted and covered by verification.
- Registry aggregation order must be deterministic. Prefer explicit module maps
  over `globals()` collection.

## Build and Emission Guardrails

- Skeleton modules may import cleanly and expose empty registries, but they must
  not change `build(ctx)` behavior.
- A module may be connected to `build(ctx)` only after:
  - its syntax constructors lower to the intended token sequence,
  - its direct dependencies are emitted or dependency-provided,
  - unresolved references fail fast during build.
- Keep registry size and total emitted proof surface distinct; emitted support
  proofs make the latter larger.

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
uv run --no-sync ruff check docs/MODULE_PLAN.md docs/PROPOSITIONAL_HILBERT_MODULES.md docs/PREDICATE_HILBERT_MODULES.md docs/ENGINEERING_GUARDRAILS.md
```

For internal-structure or import-only Python changes:

```bash
python3 -m compileall -q src/logic/propositional src/logic/predicate
uv run --no-sync ruff check src/logic/propositional src/logic/predicate docs
uv run --no-sync python -c 'from logic.propositional.hilbert import axiomatizations'
uv run --no-sync python -c 'from logic.predicate.hilbert import PredicateSystem'
```

For theorem registry changes:

```bash
uv run --no-sync ruff check .
uv run --no-sync mypy .
uv run --no-sync python -m pytest
uv run --no-sync skfd verify --level 1 metamath-logic
```

Routine theorem migrations do not edit `LEMMA_CATALOGUE.md`; it is a derived
release artifact. Before a release, regenerate it once with
`uv run --no-sync python tools/generate_lemma_catalogue.py` and validate the
checked-in result with the same command plus `--check`.

The current gate is expected to report 1,684 declared, 3,610 emitted, and 0
declared-but-unemitted proofs.

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
- Regenerate `LEMMA_CATALOGUE.md` once during release preparation after all
  Hilbert registry and lowering-filter changes have landed.

## Definition of Done

A migrated slice is done only when:

- syntax and theorem labels align with set.mm or documented aliases,
- constructors validate against the local proof registry,
- emitted artifacts verify with the configured Metamath verifier,
- dependency closure is explicit,
- module ownership is documented,
- roadmap counts and status are updated,
- tests cover the new public surface or the residual risk is stated.
