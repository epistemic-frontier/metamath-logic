# metamath-logic Module Plan

Based on `docs/LOGIC_MIGRATION_GUIDE.md` (set.mm lines 649–24571 → Python).

## Module Hierarchy

```
metamath-logic/src/logic/
  build.py
  propositional/
    core.py              ← ax-mp, ax-1, ax-2, ax-3
    implication/
      __init__.py
      basic.py           ← 公理直接应用 (a1i, a2i, mpd, id, notnot, notnotr, ...)
      syllogism.py       ← 三段论链 (syl, sylcom, syl5, syl6, 3syl, syld, ...)
      deduction.py       ← antecedent 操作 (a1d, idd, 2a1d, mpdd, mpid, ...)
      commutation.py     ← 交换 antecedent (com12, com23, com34, ...)
    truth.py              ← T./F. 常量 (df-tru, df-fal)
    negation.py           ← ¬ 演算 (con1-con4, mt2, pm2.21, ...)
    conjunction.py        ← ∧ 定义与引理 (df-an)
    disjunction.py        ← ∨ 定义与引理 (df-or, jaoi, jaod, ...)
    alt_axioms.py         ← Nicod, Meredith, Tarski-Bernays-Wajsberg
  fol/
    syntax.py             ← setvar, ∀/∃ 语法
    quantifiers.py        ← df-ex, 量词引理
    not_free.py           ← df-nf
    equality.py           ← 等号公理
    membership.py         ← ∈ 谓词逻辑
    core_schemes.py       ← 谓词演算主公理

__init__.py               ← System class + 聚合 re-export
lemmas.py                  ← 向后兼容 shim
theorems.py                ← label → function 映射表
```

## Module Size Rules

| Rule | Value |
|---|---|
| Minimum | 200 lines |
| Maximum | 800 lines |
| Exceeding | Split by mathematical sub-domain |
| Auto-create | merge_scratch.py creates new modules on demand |

## Migration Roadmap

### Phase 1: Propositional — Core (已完成 ✅)

| Module | set.mm | Status |
|---|---|---|
| core (ax-mp/ax-1/2/3) | 649–701 | ✅ |
| implication/basic | 700–900 | ✅ (34 functions) |
| negation | 12347–12391 | ✅ (27 functions) |
| disjunction | 12415–14552 | ⚠️ (6 functions) |

### Phase 2: Propositional — Implication Expansion

| Module | set.mm | Priority |
|---|---|---|
| implication/syllogism | 900–1200+ | P0 |
| implication/deduction | scattered | P0 |
| implication/commutation | 1400–1600 | P1 |

### Phase 3: Propositional — Remaining Connectives

| Module | set.mm | Priority |
|---|---|---|
| hilbert/equivalence.py | 2390–4043 | P0 |
| hilbert/conjunction.py | 4044–7288 | P0 |
| hilbert/constants.py | 11967–12295 | P1 |
| hilbert/truth_tables.py | 12296–12587 | P1 |
| hilbert/adder.py | 12588–12835 | P2 |
| hilbert/axiomatizations/ | 12836–14279 | P2 |
| hilbert/stoic.py | 14280–14552 | P2 |

#### Late Propositional Gap and Plan

The late propositional section now has skeleton modules under
`logic.propositional.hilbert`, plus a detailed map in
`docs/PROPOSITIONAL_HILBERT_MODULES.md`. These skeletons are intentionally
empty registries for now: they document ownership and import cleanly, but do
not yet change the emitted theorem set.

Current global status:
- Main `set.mm` propositional block (`523–14552`): 1742 `$p` theorem/lemma
  targets and 35 `$a` syntax/axiom/definition targets.
- Current Hilbert registry: 114 lemma constructors.
- Current lowered/exported registry lemmas: 113.
- Registered-only item: `pm2.07`, because it uses `\/` and the current lowering
  path is still mostly `-.` / `->` plus opaque `T.` / `F.` substitutions.

Late-section gap:

| set.mm section | Range | `$p` targets | `$a` targets | Target module | Current gap |
|---|---:|---:|---:|---|---|
| True and false constants | 11967–12295 | 18 | 7 | `hilbert/constants.py` | Skeleton only; strict `df-tru` bridge blocked on predicate/equality syntax |
| Truth tables | 12296–12587 | 30 | 0 | `hilbert/truth_tables.py` | Skeleton only; blocked on connective and constant coverage |
| Full adder | 12588–12835 | 24 | 4 | `hilbert/adder.py` | Skeleton only; blocked on `hadd`, `cadd`, `if-`, `w3a`, `w3o`, `wxo` support |
| Other axiomatizations | 12836–14279 | 147 | 0 | `hilbert/axiomatizations/` | Skeleton only; should remain derivability results inside Hilbert for now |
| Stoic logic | 14280–14552 | 11 | 0 | `hilbert/stoic.py` | Skeleton only; depends on conjunction and late disjunction/xor material |
| Total | 11967–14552 | 230 | 11 | — | 230 proof targets plus 11 syntax/definition targets remain in this late slice |

Execution plan:

1. Stabilize the module registry pattern.
   Each module owns a local `THEOREMS` mapping. `theorems.py` should eventually
   aggregate those maps rather than maintaining one large hand-written dict.

2. Unblock connective lowering.
   Extend emitted proof lowering for `<->`, `/\`, and `\/`; then move
   `pm2.07` from registered-only to lowered/exported.

3. Fill the dependency base before late features.
   Move biconditional helpers into `equivalence.py` and conjunction helpers
   into `conjunction.py`. These are prerequisites for truth constants, truth
   tables, adder proofs, and Stoic rules.

4. Migrate `constants.py` in two layers.
   Short term: treat `T.` and `F.` as nullary propositional constructors and
   migrate the propositional theorems around `tru`, `fal`, `trut`, `mptru`,
   `dfnot`, `inegd`, `efald`, and `pm2.21fal`.
   Long term: reconnect `df-tru` to `wal`, `cv`, and `wceq` after the
   predicate/equality package is mature.

5. Populate `truth_tables.py` after constants and connectives.
   Add truth-table theorems by connective family: implication, negation,
   biconditional, conjunction, disjunction, NAND, XOR, and NOR.

6. Defer `adder.py` until late connective syntax exists.
   The adder section needs `hadd`, `cadd`, `if-`, three-way conjunction and
   disjunction, and XOR support. Keep it isolated from the core logic registry
   until those constructors lower cleanly.

7. Keep alternative axiomatizations inside Hilbert initially.
   `minimal_implicational`, `lukasiewicz`, `meredith`, `nicod`,
   `tarski_bernays_wajsberg`, and `russell_bernays` are currently bridge
   theorems proving derivability/equivalence inside the standard Hilbert
   environment. Only create independent proof-system packages later if we need
   separately runnable kernels.

8. Populate `stoic.py` last.
   Stoic logic depends on conjunction, disjunction, XOR, and several natural
   deduction-style helpers. It should be migrated after the late connective
   dependency closure is explicit.

### Phase 4: FOL / Predicate Calculus (set.mm 14553–24577)

Tarski's system S2: propositional axioms plus `ax-gen`, `ax-4` through
`ax-9`. Metalogical/scheme completeness is added by the auxiliary schemes
`ax-10` through `ax-13`.

`set.mm` also introduces three predicate/equality dependencies before the main
FOL section for the `df-tru` trick: `wal`, `cv`, and `wceq` at lines
12017, 12081, and 12114. Treat these as predicate package ownership even
though their declarations occur in the propositional tail.

Current global status:
- Main FOL block (`14553–24577`): 901 `$p` theorem/lemma targets and 22 `$a`
  syntax/axiom/definition targets.
- Pre-FOL predicate dependencies (`11990–12114`): 3 additional `$a` targets
  (`wal`, `cv`, `wceq`).
- Current `logic.predicate.hilbert` implementation: token/constructor skeleton
  plus placeholder `AX5` through `AX13`.
- Missing from emitted artifacts: predicate theorem registry, `ax-gen`,
  `ax-4`, strict `setvar`/`class`/`wff` type separation, `$d` side conditions,
  and build integration for predicate assertions.

Detailed package map: `docs/PREDICATE_HILBERT_MODULES.md`.

#### Predicate Package Layout

```
metamath-logic/src/logic/predicate/hilbert/
  _builtins.py
  _structures.py
  system.py
  syntax.py
  quantifiers.py
  not_free.py
  equality.py
  substitution.py
  membership.py
  core_schemes.py
  uniqueness.py
  theorems.py
  axiomatizations/
    __init__.py
    aristotle.py
    intuitionistic.py
```

| Module | set.mm range | Content | Priority |
|---|---:|---|---|
| `syntax.py` | 11990–12114, 14626–14744, 16215–16283, 17848–17914 | `setvar`, `class`, `wal`, `cv`, `wceq`, `wex`, `wnf`, `weq`, `wel`, `wsb` ownership and typing discipline | P0 |
| `quantifiers.py` | 14661–15649, 15687–16214 | `df-ex`, `ax-gen`, `ax-4`, `ax-5`, `al*`, `ex*`, `19.*`, specialization and generalization helpers | P0 |
| `not_free.py` | 14697–16214, scattered later | `df-nf`, `nf*`, `hb*`, nonfreeness transport and distinct-variable support | P0 |
| `equality.py` | 16215–17349 | `weq`, `ax-6`, `ax-7`, equality identity/transitivity/transport helpers | P0 |
| `substitution.py` | 17350–17847, 18699–20616 | `wsb`, `df-sb`, proper substitution, `ax-12` dependency closure | P1 |
| `membership.py` | 17848–18124 | `wel`, `ax-8`, `ax-9`, membership equality transport | P1 |
| `core_schemes.py` | 18125–22473 | redundancy bridges plus `ax-10`, `ax-11`, `ax-12`, `ax-13` and scheme-completeness helpers | P1 |
| `uniqueness.py` | 22474–23854 | at-most-one and unique-existence quantifiers and theorems | P2 |
| `axiomatizations/aristotle.py` | 23855–24449 | Aristotelian assertic syllogisms in modern predicate notation | P2 |
| `axiomatizations/intuitionistic.py` | 24450–24577 | intuitionistic axiom-name aliases/comparison theorems | P2 |

#### Predicate Gap by Section

| set.mm section | Range | `$p` targets | `$a` targets | Primary module |
|---|---:|---:|---:|---|
| Pre-FOL deps for `df-tru` | 11990–12114 | 0 | 3 | `syntax.py` |
| Existential + not-free intro | 14626–14811 | 12 | 4 | `syntax.py`, `quantifiers.py`, `not_free.py` |
| `ax-gen`, `ax-4`, quantifier basics | 14812–15649 | 109 | 2 | `quantifiers.py` |
| Empty domain note | 15650–15686 | 4 | 0 | `quantifiers.py` |
| `ax-5` distinctness | 15687–16214 | 51 | 1 | `not_free.py`, `quantifiers.py` |
| Equality predicate continued | 16215–16283 | 5 | 0 | `equality.py` |
| `ax-6` existence | 16284–16699 | 40 | 1 | `equality.py` |
| `ax-7` equality | 16700–17349 | 56 | 1 | `equality.py` |
| Proper substitution | 17350–17847 | 43 | 2 | `substitution.py` |
| Membership predicate | 17848–17914 | 1 | 1 | `membership.py` |
| `ax-8` membership left equality | 17915–18018 | 7 | 1 | `membership.py` |
| `ax-9` membership right equality | 18019–18124 | 9 | 1 | `membership.py` |
| Redundancy of `ax-10`..`ax-13` | 18125–18375 | 13 | 0 | `core_schemes.py` |
| Auxiliary schemes `ax-10`..`ax-13` | 18376–22473 | 383 | 4 | `core_schemes.py`, `substitution.py` |
| Uniqueness and unique existence | 22474–23854 | 123 | 4 | `uniqueness.py` |
| Other predicate axiomatizations | 23855–24449 | 30 | 0 | `axiomatizations/aristotle.py` |
| Intuitionistic logic aliases | 24450–24577 | 15 | 0 | `axiomatizations/intuitionistic.py` |

#### FOL Axiom Index

| Axiom | Name | set.mm | Module |
|---|---|---:|---|
| `ax-gen` | Generalization | 14832 | `quantifiers.py` |
| `ax-4` | Quantified implication | 14959 | `quantifiers.py` |
| `ax-5` | Distinctness | 15706 | `quantifiers.py`, `not_free.py` |
| `ax-6` | Existence | 16303 | `equality.py` |
| `ax-7` | Equality | 16719 | `equality.py` |
| `ax-8` | Left equality for membership | 17932 | `membership.py` |
| `ax-9` | Right equality for membership | 18035 | `membership.py` |
| `ax-10` | Quantified negation | 18423 | `core_schemes.py` |
| `ax-11` | Quantifier commutation | 18550 | `core_schemes.py` |
| `ax-12` | Substitution | 18736 | `substitution.py`, `core_schemes.py` |
| `ax-13` | Quantified equality | 20640 | `core_schemes.py` |

#### Predicate Migration Order

1. Make the predicate syntax layer real.
   Add strict type ownership for `setvar`, `class`, and `wff`; preserve the
   pre-FOL declarations `wal`, `cv`, and `wceq`; and introduce a representation
   for `$d` constraints.

2. Connect predicate assertions to `logic.build`.
   Emit at least `wal`, `wex`, `wnf`, `weq`, `wel`, `ax-gen`, and
   `ax-4` through `ax-9` before migrating theorem bodies.

3. Create `SETMM_TO_PREDICATE_THEOREMS`.
   Mirror the propositional registry pattern with module-local `THEOREMS`
   maps and one aggregate `theorems.py`.

4. Migrate quantifier and nonfreeness hubs first.
   `quantifiers.py` and `not_free.py` are the dependency base for equality,
   substitution, uniqueness, and set theory.

5. Migrate equality and membership next.
   These are the bridge from FOL into ZF set theory: `weq`, `wel`,
   `ax-6`, `ax-7`, `ax-8`, and `ax-9`.

6. Defer full substitution and auxiliary schemes until the base is stable.
   `df-sb`, `ax-10`..`ax-13`, and their closure contain the largest proof
   dependency surface.

7. Keep uniqueness and alternative axiomatizations late.
   They are useful, but they should not block the language bridge required by
   set theory.

## Current Task: propcalc-migration

Scope: pm2.37–pm2.75 (Phase 1 gap-filling).
When complete, these will fill into existing modules:
- pm2.37–43 → implication/basic
- pm2.45–65 → negation
- pm2.67–75 → disjunction
