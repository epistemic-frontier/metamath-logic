from __future__ import annotations

import logging

from skfd.api_v2 import BuildContextV2
from skfd.authoring.emit import emit_axioms, emit_lowered_lemmas
from skfd.builder_v2 import MMBuilderV2
from skfd.core.symbols import SymbolId
from logic.propositional.hilbert import System
from logic.propositional.hilbert._structures import Imp, phi, psi
from logic.propositional.hilbert.lemmas import Proof
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS

_log = logging.getLogger(__name__)


def _emit_rule_skeleton(mm: MMBuilderV2, system: System, *, provable: SymbolId) -> None:
    phi_wff = system.compile(phi, ctx="rule[mp.phi]")
    psi_wff = system.compile(psi, ctx="rule[mp.psi]")
    imp_wff = system.compile(Imp(phi, psi), ctx="rule[mp.imp]")

    with mm.block():
        mm.e(mm.sym.label("ax-mp.1"), tc=provable, expr=phi_wff.tokens)
        mm.e(mm.sym.label("ax-mp.2"), tc=provable, expr=imp_wff.tokens)
        mm.a(mm.sym.label("ax-mp"), tc=provable, expr=psi_wff.tokens)


def build(ctx: BuildContextV2) -> None:
    mm = ctx.mm
    prelude = ctx.deps["metamath-prelude"]

    system = System.make(interner=mm.interner, names=ctx.names)
    builtins = system.builtins
    coverage = getattr(ctx, "coverage", None)
    if coverage is not None:
        coverage.declare_registry("hilbert", SETMM_TO_HILBERT_LEMMAS)

    wff = prelude["wff"]
    provable = prelude["|-"]

    ax_1 = mm.sym.label("ax-1")
    ax_2 = mm.sym.label("ax-2")
    ax_3 = mm.sym.label("ax-3")
    ax_mp = mm.sym.label("ax-mp")

    emit_axioms(
        mm,
        system,
        typecode=provable,
        label_ids={"A1": ax_1, "A2": ax_2, "A3": ax_3},
    )
    _emit_rule_skeleton(mm, system, provable=provable)

    ph = prelude["ph"]
    ps = prelude["ps"]
    mm.auto.use_existing_floating(ph, label=prelude["wph"])
    mm.auto.use_existing_floating(ps, label=prelude["wps"])

    wo = mm.sym.label("wo")
    wtru = mm.sym.label("wtru")
    wfal = mm.sym.label("wfal")
    idi = mm.sym.label("idi")
    a1ii = mm.sym.label("a1ii")

    mm.a(wo, tc=wff, expr=[builtins.lp, ph, builtins.or_, ps, builtins.rp])
    mm.a(wtru, tc=wff, expr=[builtins.tru])
    mm.a(wfal, tc=wff, expr=[builtins.fal])

    with mm.block():
        mm.e(mm.sym.label("idi.1"), tc=provable, expr=[ph])
        mm.p(idi, tc=provable, expr=[ph], proof=[mm.sym.label("idi.1")])

    with mm.block():
        mm.e(mm.sym.label("a1ii.1"), tc=provable, expr=[ph])
        mm.e(mm.sym.label("a1ii.2"), tc=provable, expr=[ps])
        mm.p(a1ii, tc=provable, expr=[ph], proof=[mm.sym.label("a1ii.1")])

    compiled_axioms = system.compile_axioms()
    reserved = {"wi", "wn", "wtru", "wfal"}
    # Tokens for which a proof has an emittable lowering path. Disjunction is
    # declared above, but it is not listed here: proving a ∨-stated theorem
    # (e.g. pm2.07) requires df-or plus biconditional rewriting, which this
    # pure ¬/→ Hilbert lowering path does not provide. The nullary top/bottom
    # constants T. / F. are emittable because they only appear as opaque
    # substitution targets during ref-unification.
    supported_tokens = {
        builtins.neg,
        builtins.imp,
        builtins.tru,
        builtins.fal,
        builtins.lp,
        builtins.rp,
    }
    # Propositional variables that have a floating hypothesis in the prelude.
    floating_by_var = {
        prelude["ph"]: prelude["wph"],
        prelude["ps"]: prelude["wps"],
        prelude["ch"]: prelude["wch"],
        prelude["th"]: prelude["wth"],
        prelude["ta"]: prelude["wta"],
    }

    def _refs(p: Proof) -> set[str]:
        refs: set[str] = set()
        for st in getattr(p, "steps", ()):
            if getattr(st, "op", None) == "ref":
                r = getattr(st, "ref", None)
                if isinstance(r, str) and r:
                    refs.add(r)
        return refs

    def _emittable(p: Proof) -> bool:
        """A proof is emittable only if every token is a supported connective
        (¬, →, parens) or a propositional variable with a floating hypothesis.
        Proofs stated with e.g. ∨ cannot be lowered until the logic package has
        a df-or based lowering path."""
        for st in getattr(p, "steps", ()):
            w = getattr(st, "wff", None)
            if w is None:
                continue
            for t in w.tokens:
                if t in supported_tokens or t in floating_by_var:
                    continue
                return False
        return True

    # Emit the maximal subset of the declared registry. Drop:
    #   - construction failures (e.g. syl5com: "mp: antecedent mismatch"),
    #   - proofs using a connective outside this lowering subset (e.g. pm2.07 uses ∨),
    #   - anything that transitively depends on an excluded theorem.
    constructed: dict[str, Proof] = {}
    excluded: dict[str, str] = {}
    for name, ctor in SETMM_TO_HILBERT_LEMMAS.items():
        try:
            p = ctor(system)
        except Exception as exc:
            excluded[name] = f"construction failed: {exc}"
            continue
        if not _emittable(p):
            excluded[name] = "uses a connective outside the lowering subset"
            continue
        constructed[name] = p

    changed = True
    while changed:
        changed = False
        for name in list(constructed):
            for ref in _refs(constructed[name]):
                if ref in SETMM_TO_HILBERT_LEMMAS and ref not in constructed:
                    excluded[name] = f"depends on excluded theorem {ref!r}"
                    del constructed[name]
                    changed = True
                    break

    unresolved: set[str] = set()
    for p in constructed.values():
        for ref in _refs(p):
            if ref in compiled_axioms or ref in reserved or ref in constructed:
                continue
            unresolved.add(ref)
    if unresolved:
        raise ValueError(f"unresolved lemma references: {sorted(unresolved)}")

    if excluded:
        _log.info(
            "emitting %d/%d declared theorems; excluded %d: %s",
            len(constructed),
            len(SETMM_TO_HILBERT_LEMMAS),
            len(excluded),
            "; ".join(f"{n} ({r})" for n, r in sorted(excluded.items())),
        )

    lemmas = list(constructed.values())
    emit_lowered_lemmas(
        mm,
        system,
        lemmas,
        typecode=provable,
        wff_typecode=wff,
        label_ids={
            "wi": prelude["wi"],
            "wn": prelude["wn"],
            "wtru": wtru,
            "wfal": wfal,
            "mp": ax_mp,
            "A1": ax_1,
            "A2": ax_2,
            "A3": ax_3,
        },
        floating_by_var=floating_by_var,
    )

    export_labels = [
        "wo",
        "wtru",
        "wfal",
        "idi",
        "a1ii",
        "ax-1",
        "ax-2",
        "ax-3",
        "ax-mp",
        *sorted(constructed.keys()),
    ]
    mm.export(*(mm.sym.label(n) for n in export_labels))
