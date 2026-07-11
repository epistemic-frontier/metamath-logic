# metamath-logic Migration Guide (set.mm → Python packages)

## Source of truth: local set.mm snapshot

This guide currently uses:
- local file: [set.mm](file:///Users/mingli/MetaMath/set.mm/set.mm)
- downloaded: **2026-07-11**
- SHA-256: `131fe655a925826c960e57684fe8a73c5ae46d43814b043a1d64457b01130abd`

All line numbers below refer to that exact file. If the snapshot changes,
update the digest and regenerate the line ranges.

## Scope and boundaries

### Prelude vs Logic boundary (within first 700 lines)

- Foundation prelude: the ambient part of `set.mm` **lines 1–648**
  (`wff`, `|-`, schema variables and `$f`, `wn`, `wi`)
- Logic: ordinary proof/syntax content, including `idi`, `a1ii`, `wo`,
  `wtru`, `wfal`, and the `ax-mp` / `ax-1..3` block.

Reference:
- `ax-mp` block begins: [set.mm:L649](file:///Users/mingli/MetaMath/set.mm/set.mm#L649)

### Logic package boundary inside set.mm (the "set-pred.mm" monolith)

In the upstream modularization scheme, `set.mm` marks “logic” as the virtual file `set-pred.mm`:
- Begin marker: [set.mm:L311](file:///Users/mingli/MetaMath/set.mm/set.mm#L311)
- End marker: [set.mm:L24944](file:///Users/mingli/MetaMath/set.mm/set.mm#L24944)

Operationally, for this project:
- `metamath-prelude` covers only the global foundation scope: base typecodes,
  schema variables and floating hypotheses, `wn`, and `wi`.
- `metamath-logic` covers the remainder of `set-pred.mm`, i.e. **649–24944**, including both:
  - propositional calculus library
  - first-order predicate calculus with equality (and the “setvar” language needed by set theory)
- The helper labels `idi` and `a1ii` are historically before line 649, but are
  owned by `metamath-logic` because they use local `$e` hypotheses and are not
  foundation-scope mechanics.

## Migration strategy (why we split, and what each split guarantees)

We split the ~24k-line logic monolith into Python modules (and optionally further into SKFD packages) for three reasons:
- Tight verification loops: each chunk should be verifiable independently.
- Stable interfaces: each chunk has a minimal `export` surface that downstream packages can depend on.
- Better retrieval for proof generation: theorems live close to their prerequisites, and dependency layering is explicit.

For each chunk below, we define:
- **set.mm range** (line interval)
- **Python file(s)** inside `metamath-logic`
- **Exports** (what downstream packages should import by label)
- **Dependency contract** (what this chunk may assume exists)

## Implemented file layout inside metamath-logic

The earlier proposed `core.py`/`fol/` split was a migration sketch. The current
authoritative layout is:

```
metamath-logic/src/logic/
  build.py
  propositional/hilbert/  # connective modules, axioms, registry, System facade
  predicate/hilbert/
    __init__.py           # PredicateSystem facade
    _builtins.py
    _structures.py
    _internal.py
    axioms.py
    lemmas.py
    theorems.py
```

Notes:
- `build.py` is the single orchestrator used by the SKFD driver for `metamath-logic`.
- The `propositional/*` directory is intended to be “term-free” and should not require `setvar`.
- `predicate/hilbert` introduces quantifiers and predicate machinery and is the
  bridge to set theory. Predicate `system.py` and `definitions.py` do not exist.

## Historical range plan

The paths and recommended exports below preserve the original migration plan;
they are not the current file map. For the implemented layout and status, use
`MODULE_PLAN.md`, `PROPOSITIONAL_HILBERT_MODULES.md`, and
`PREDICATE_HILBERT_MODULES.md`.

### 1) Propositional calculus core axioms and rule

- **set.mm range**: **649–701**
- **Anchor lines**:
  - `ax-mp` block begins: [set.mm:L649](file:///Users/mingli/MetaMath/set.mm/set.mm#L649)
  - `ax-1..ax-3`: [set.mm:L679-L701](file:///Users/mingli/MetaMath/set.mm/set.mm#L679-L701)
- **Python**: `logic/propositional/core.py`
- **Exports**:
  - `ax-mp`, `ax-1`, `ax-2`, `ax-3`
  - keep the labels identical to set.mm
- **Dependency contract**:
  - requires `metamath-prelude` exports: `wff`, `|-`, `ph/ps/ch`, `wph/wps/wch`, `wn`, `wi`

### 2) Implication-only library (intuitionistic/minimal implicational calculus)

- **set.mm range**: **706–1631**
- **Anchor lines**:
  - Section header: [set.mm:L706](file:///Users/mingli/MetaMath/set.mm/set.mm#L706)
  - This region should avoid `ax-3` where possible (set.mm explicitly calls this out).
- **Python**: `logic/propositional/implication.py`
- **Exports (minimum recommended)**:
  - high-frequency infrastructure theorems/rules: `a1i`, `a2i`, `mpd`, `syl`, `mp2`, `mp2b`, `mp1i`
  - plus any lemma that becomes a proof-search “hub” for later sections
- **Dependency contract**:
  - allowed: `ax-mp`, `ax-1`, `ax-2`
  - avoid: `ax-3` (unless explicitly placing a lemma in the “classical” chunk)

### 3) True/False constants (and universal quantifier introduced for df-tru)

- **set.mm range**: **12135–12463**
- **Anchor lines**:
  - Section header: [set.mm:L12135](file:///Users/mingli/MetaMath/set.mm/set.mm#L12135)
  - Universal quantifier subsection: [set.mm:L12142](file:///Users/mingli/MetaMath/set.mm/set.mm#L12142)
  - Equality predicate subsection: [set.mm:L12195](file:///Users/mingli/MetaMath/set.mm/set.mm#L12195)
  - False constant subsection: [set.mm:L12385](file:///Users/mingli/MetaMath/set.mm/set.mm#L12385)
- **Python**: `logic/propositional/truth.py`
- **Exports**:
  - `T.` / `F.` related definitions (`df-tru`, `df-fal`) and the minimal supporting lemmas you decide to keep
- **Dependency contract**:
  - this is a bridge point: it introduces `A.` and `wal` for the “df-tru trick”.
  - keep it isolated so that pure propositional packages can stay quantifier-free.

### 4) Negation

- **set.mm range**: **1632–2410**
- **Anchor lines**:
  - Section header: [set.mm:L1632](file:///Users/mingli/MetaMath/set.mm/set.mm#L1632)
- **Python**: `logic/propositional/negation.py`
- **Exports (minimum recommended)**:
  - core negation transformations required by later connectives and by predicate calculus: double-negation laws, contraposition helpers, etc.
- **Dependency contract**:
  - classical part will typically rely on `ax-3`
  - if you want an intuitionistic subset, keep it in a separate submodule and label it explicitly

### 5) Conjunction

- **set.mm range**: **4049–7376**
- **Anchor lines**:
  - Section header: [set.mm:L4049](file:///Users/mingli/MetaMath/set.mm/set.mm#L4049)
- **Python**: `logic/propositional/conjunction.py`
- **Exports**:
  - `df-an` and foundational lemmas (only once `df-an` exists)
- **Dependency contract**:
  - depends on negation/disjunction equivalences if you define conjunction via De Morgan variants

### 6) Disjunction (and the remaining propositional library)

- **set.mm range**: **7377–14720**
- **Anchor lines**:
  - Disjunction section: [set.mm:L7377](file:///Users/mingli/MetaMath/set.mm/set.mm#L7377)
  - Other axiomatizations: [set.mm:L13004](file:///Users/mingli/MetaMath/set.mm/set.mm#L13004)
  - Stoic logic: [set.mm:L14448](file:///Users/mingli/MetaMath/set.mm/set.mm#L14448)
  - Predicate calculus begins at: [set.mm:L14721](file:///Users/mingli/MetaMath/set.mm/set.mm#L14721)
- **Python**:
  - `logic/propositional/disjunction.py`
  - `logic/propositional/alt_axioms.py` (for alternative axiomatizations like Nicod/Meredith/Tarski-Bernays-Wajsberg, etc., if you keep them)
- **Exports**:
  - `df-or` + derived theorems used later
  - only export “hubs”; keep proof-search noise internal

### 7) Predicate calculus with equality (Tarski’s S2 and supporting schemes)

- **set.mm range**: **14721–24944**
- **Anchor lines**:
  - Predicate calculus section header: [set.mm:L14721](file:///Users/mingli/MetaMath/set.mm/set.mm#L14721)
  - Existential quantifier: [set.mm:L14829](file:///Users/mingli/MetaMath/set.mm/set.mm#L14829)
  - Generalization rule scheme: [set.mm:L14980](file:///Users/mingli/MetaMath/set.mm/set.mm#L14980)
  - Auxiliary axiom schemes: [set.mm:L18739](file:///Users/mingli/MetaMath/set.mm/set.mm#L18739)
  - End marker: [set.mm:L24944](file:///Users/mingli/MetaMath/set.mm/set.mm#L24944)
- **Python** (suggested split):
  - `logic/fol/syntax.py` (setvar pool + wff formation rules for `A.`/`E.` and atomic predicates)
  - `logic/fol/quantifiers.py` (df-ex and quantifier manipulation lemmas)
  - `logic/fol/not_free.py` (df-nf + nf lemmas)
  - `logic/fol/equality.py` (equality axioms and substitution machinery)
  - `logic/fol/membership.py` (`e.` as a predicate, and its logic-level interaction rules)
  - `logic/fol/core_schemes.py` (the main axiom schemes/rules for predicate calculus)
- **Exports**:
  - The minimal “language bridge” required by set theory packages:
    - `setvar` and a stable setvar pool (`x y z w v u t ...`)
    - quantifier syntax and definitions used pervasively in set theory
    - equality and membership wff formation rules (`weq`, `wel`) and their core logical principles
- **Dependency contract**:
  - depends on propositional core (implication/negation) and the True/False layer if you keep df-tru/df-fal as in set.mm

## Migration workflow (repeatable steps)

For each chunk:
1. Create the target Python module file(s) under `metamath-logic/src/logic/...`.
2. Implement a “chunk builder” function that emits only the assertions in that chunk.
3. Add `mm.export(...)` for the chunk’s public surface; keep internal lemmas unexported.
4. Verify the chunk in isolation, then in the full monolith:
   - `uv run --no-sync skfd verify --level 1 metamath-logic`
   - `uv run --no-sync mypy src`

## Practical guidance for keeping labels stable

- Use set.mm label spelling for exported assertions (`ax-mp`, `ax-1`, `df-ex`, …).
- Keep all syntax/primitive tokens interned under a global stable module id (the prelude already does this for base tokens).
- When lowering proofs, use dependency-provided label `SymbolId`s where applicable (to avoid accidental duplicate labels).

The migration is now fully emitted: the latest verification reports 1,684
declared proofs, 3,610 emitted proofs, and 0 declared-but-unemitted;
`mmverify`, `metamath`, and `knife` all pass.
