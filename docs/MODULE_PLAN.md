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
| truth (T./F.) | 11967–12346 | P1 |
| conjunction (∧) | 12392–12414 | P1 |
| disjunction (bulk) | 12415–14552 | P1 |
| alt_axioms | scattered | P2 |

### Phase 4: FOL / Predicate Calculus (set.mm 14553–24571)

Tarski's system S2: propositional axioms + ax-gen, ax-4 through ax-9.
Metalogical completeness added via ax-10 through ax-13.

| Module | set.mm | Content | Priority |
|---|---|---|---|
| fol/syntax | 14553–14680 | setvar pool (x,y,z,w,v,u,t), $d statements, wal syntax, weq/wel formation | P1 |
| fol/quantifiers | 14680– | ax-gen, ax-4/5/6, df-ex, 19.* theorems, universal/existential manipulation | P1 |
| fol/equality | — | ax-7/8/9, equality substitution, equequivalence rules | P1 |
| fol/not_free | — | df-nf, nf-* theorems, free-variable reasoning | P2 |
| fol/membership | — | ∈ as predicate, wel formation, elementary membership logic | P2 |
| fol/core_schemes | — | ax-10/11/12/13, scheme completeness theorems | P1 |
| fol/distinctors | — | $d manipulation, distinct variable conditions | P2 |

#### FOL Axiom Index

| Axiom | Name | set.mm | Module |
|---|---|---|---|
| ax-gen | Generalization | L14824 | quantifiers |
| ax-4 | Universal quantifier distribution | — | quantifiers |
| ax-5 | Quantified implication | — | quantifiers |
| ax-6 | Quantified negation | — | quantifiers |
| ax-7 | Equality reflexivity | — | equality |
| ax-8 | Equality substitution (left) | — | equality |
| ax-9 | Equality substitution (right) | — | equality |
| ax-10 | Quantifier swap | — | core_schemes |
| ax-11 | Quantifier commutation | — | core_schemes |
| ax-12 | Substitution | — | core_schemes |
| ax-13 | Quantified equality | — | core_schemes |

## Current Task: propcalc-migration

Scope: pm2.37–pm2.75 (Phase 1 gap-filling).
When complete, these will fill into existing modules:
- pm2.37–43 → implication/basic
- pm2.45–65 → negation
- pm2.67–75 → disjunction
