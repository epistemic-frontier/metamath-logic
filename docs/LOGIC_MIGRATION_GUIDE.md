# metamath-logic Migration Guide (set.mm → Python packages)

## Source-of-truth: set.mm git hash

This guide is pinned to:
- `set.mm` repository commit: **357fdac63fc0f61f70c16a6bb10ab0b629543fa5**
- File: [set.mm](file:///Users/mingli/MetaMath/set.mm/set.mm)

All line numbers below refer to this exact commit of `set.mm`. If you change the `set.mm` checkout, you must regenerate the line ranges.

## Scope and boundaries

### Prelude vs Logic boundary (within first 700 lines)

- Prelude: `set.mm` **lines 1–648**
- Logic: starts at `set.mm` **line 649** (the `ax-mp` block begins)

Reference:
- `ax-mp` block begins: [set.mm:L649](file:///Users/mingli/MetaMath/set.mm/set.mm#L649)

### Logic package boundary inside set.mm (the "set-pred.mm" monolith)

In the upstream modularization scheme, `set.mm` marks “logic” as the virtual file `set-pred.mm`:
- Begin marker: [set.mm:L311](file:///Users/mingli/MetaMath/set.mm/set.mm#L311)
- End marker: [set.mm:L24571](file:///Users/mingli/MetaMath/set.mm/set.mm#L24571)

Operationally, for this project:
- `metamath-prelude` covers the portion of `set-pred.mm` that is pure syntax/bootstrap (currently 1–648).
- `metamath-logic` is responsible for the remainder of `set-pred.mm`, i.e. **649–24571**, and must eventually include both:
  - propositional calculus library
  - first-order predicate calculus with equality (and the “setvar” language needed by set theory)

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

## Proposed file layout inside metamath-logic

Target layout (planned; current code may implement only a subset):

```
metamath-logic/src/logic/
  build.py
  propositional/
    core.py
    implication.py
    truth.py
    negation.py
    conjunction.py
    disjunction.py
    alt_axioms.py
  fol/
    syntax.py
    quantifiers.py
    not_free.py
    equality.py
    membership.py
    core_schemes.py
```

Notes:
- `build.py` is the single orchestrator used by the SKFD driver for `metamath-logic`.
- The `propositional/*` directory is intended to be “term-free” and should not require `setvar`.
- The `fol/*` directory introduces `setvar`, quantifiers, and predicate machinery; it is the required bridge to set theory.

## Mapping: set.mm ranges → metamath-logic files

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

- **set.mm range**: **704–11966**
- **Anchor lines**:
  - Section header: [set.mm:L704-L717](file:///Users/mingli/MetaMath/set.mm/set.mm#L704-L717)
  - This region should avoid `ax-3` where possible (set.mm explicitly calls this out).
- **Python**: `logic/propositional/implication.py`
- **Exports (minimum recommended)**:
  - high-frequency infrastructure theorems/rules: `a1i`, `a2i`, `mpd`, `syl`, `mp2`, `mp2b`, `mp1i`
  - plus any lemma that becomes a proof-search “hub” for later sections
- **Dependency contract**:
  - allowed: `ax-mp`, `ax-1`, `ax-2`
  - avoid: `ax-3` (unless explicitly placing a lemma in the “classical” chunk)

### 3) True/False constants (and universal quantifier introduced for df-tru)

- **set.mm range**: **11967–12346**
- **Anchor lines**:
  - Section header: [set.mm:L11967](file:///Users/mingli/MetaMath/set.mm/set.mm#L11967)
  - Universal quantifier token: [set.mm:L11991](file:///Users/mingli/MetaMath/set.mm/set.mm#L11991)
  - `wal` syntax axiom: [set.mm:L12017](file:///Users/mingli/MetaMath/set.mm/set.mm#L12017)
  - False constant section header: [set.mm:L12217-L12221](file:///Users/mingli/MetaMath/set.mm/set.mm#L12217-L12221)
- **Python**: `logic/propositional/truth.py`
- **Exports**:
  - `T.` / `F.` related definitions (`df-tru`, `df-fal`) and the minimal supporting lemmas you decide to keep
- **Dependency contract**:
  - this is a bridge point: it introduces `A.` and `wal` for the “df-tru trick”.
  - keep it isolated so that pure propositional packages can stay quantifier-free.

### 4) Negation

- **set.mm range**: **12347–12391**
- **Anchor lines**:
  - Section header: [set.mm:L12347](file:///Users/mingli/MetaMath/set.mm/set.mm#L12347)
- **Python**: `logic/propositional/negation.py`
- **Exports (minimum recommended)**:
  - core negation transformations required by later connectives and by predicate calculus: double-negation laws, contraposition helpers, etc.
- **Dependency contract**:
  - classical part will typically rely on `ax-3`
  - if you want an intuitionistic subset, keep it in a separate submodule and label it explicitly

### 5) Conjunction

- **set.mm range**: **12392–12414**
- **Anchor lines**:
  - Section header: [set.mm:L12392](file:///Users/mingli/MetaMath/set.mm/set.mm#L12392)
- **Python**: `logic/propositional/conjunction.py`
- **Exports**:
  - `df-an` and foundational lemmas (only once `df-an` exists)
- **Dependency contract**:
  - depends on negation/disjunction equivalences if you define conjunction via De Morgan variants

### 6) Disjunction (and the bulk propositional library that follows)

- **set.mm range**: **12415–14552**
- **Anchor lines**:
  - Section header: [set.mm:L12415](file:///Users/mingli/MetaMath/set.mm/set.mm#L12415)
  - Predicate calculus begins at: [set.mm:L14553](file:///Users/mingli/MetaMath/set.mm/set.mm#L14553)
- **Python**:
  - `logic/propositional/disjunction.py`
  - `logic/propositional/alt_axioms.py` (for alternative axiomatizations like Nicod/Meredith/Tarski-Bernays-Wajsberg, etc., if you keep them)
- **Exports**:
  - `df-or` + derived theorems used later
  - only export “hubs”; keep proof-search noise internal

### 7) Predicate calculus with equality (Tarski’s S2 and supporting schemes)

- **set.mm range**: **14553–24571**
- **Anchor lines**:
  - Predicate calculus section header: [set.mm:L14553](file:///Users/mingli/MetaMath/set.mm/set.mm#L14553)
  - `setvar` declarations: [set.mm:L14635-L14656](file:///Users/mingli/MetaMath/set.mm/set.mm#L14635-L14656)
  - Existential quantifier: [set.mm:L14665-L14676](file:///Users/mingli/MetaMath/set.mm/set.mm#L14665-L14676)
  - Generalization axiom scheme: [set.mm:L14824-L14833](file:///Users/mingli/MetaMath/set.mm/set.mm#L14824-L14833)
  - End marker: [set.mm:L24571](file:///Users/mingli/MetaMath/set.mm/set.mm#L24571)
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
   - `uv run python -m skfd.cli verify metamath-logic`
   - `uv run mypy src`

## Practical guidance for keeping labels stable

- Use set.mm label spelling for exported assertions (`ax-mp`, `ax-1`, `df-ex`, …).
- Keep all syntax/primitive tokens interned under a global stable module id (the prelude already does this for base tokens).
- When lowering proofs, use dependency-provided label `SymbolId`s where applicable (to avoid accidental duplicate labels).

