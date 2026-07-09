from __future__ import annotations

import logging

from skfd.api_v2 import BuildContextV2
from skfd.authoring.emit import emit_axioms, emit_lowered_lemmas
from skfd.builder_v2 import MMBuilderV2
from skfd.core.symbols import SymbolId

from logic.predicate.hilbert._builtins import PredicateBuiltins
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
    ch = prelude["ch"]
    mm.auto.use_existing_floating(ph, label=prelude["wph"])
    mm.auto.use_existing_floating(ps, label=prelude["wps"])
    mm.auto.use_existing_floating(ch, label=prelude["wch"])

    wo = mm.sym.label("wo")
    wa = mm.sym.label("wa")
    wtru = mm.sym.label("wtru")
    wfal = mm.sym.label("wfal")
    wb = mm.sym.label("wb")
    idi = mm.sym.label("idi")
    a1ii = mm.sym.label("a1ii")
    df_fal = mm.sym.label("df-fal")

    mm.a(wo, tc=wff, expr=[builtins.lp, ph, builtins.or_, ps, builtins.rp])
    mm.a(wa, tc=wff, expr=[builtins.lp, ph, builtins.and_, ps, builtins.rp])
    mm.a(wtru, tc=wff, expr=[builtins.tru])
    mm.a(wfal, tc=wff, expr=[builtins.fal])
    mm.a(
        df_fal,
        tc=provable,
        expr=[builtins.lp, builtins.fal, builtins.iff, builtins.neg, builtins.tru, builtins.rp],
    )
    mm.a(wb, tc=wff, expr=[builtins.lp, ph, builtins.iff, ps, builtins.rp])

    w3a_label = mm.sym.label("w3a")
    mm.a(
        w3a_label, tc=wff, expr=[builtins.lp, ph, builtins.and_, ps, builtins.and_, ch, builtins.rp]
    )

    w3o_label = mm.sym.label("w3o")
    mm.a(w3o_label, tc=wff, expr=[builtins.lp, ph, builtins.or_, ps, builtins.or_, ch, builtins.rp])

    wnan_label = mm.sym.label("wnan")
    mm.a(wnan_label, tc=wff, expr=[builtins.lp, ph, builtins.nand, ps, builtins.rp])

    wnor_label = mm.sym.label("wnor")
    mm.a(wnor_label, tc=wff, expr=[builtins.lp, ph, builtins.nor, ps, builtins.rp])

    wcad_label = mm.sym.label("wcad")
    mm.a(wcad_label, tc=wff, expr=[builtins.cadd, ph, ps, ch])

    wxo_label = mm.sym.label("wxo")
    mm.a(wxo_label, tc=wff, expr=[builtins.lp, ph, builtins.xor, ps, builtins.rp])

    whad_label = mm.sym.label("whad")
    mm.a(whad_label, tc=wff, expr=[builtins.had, ph, ps, ch])

    wif_label = mm.sym.label("wif")
    mm.a(wif_label, tc=wff, expr=[builtins.if_, ph, ps, ch])

    # Predicate syntax: class variables + wcel
    LOGIC_MODULE = "logic"
    cA = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="cA", kind="Var", origin_ref=0
    )
    cB = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="cB", kind="Var", origin_ref=0
    )
    wcel_cA = mm.f(mm.sym.label("wcel.cA"), tc=wff, var=cA)
    wcel_cB = mm.f(mm.sym.label("wcel.cB"), tc=wff, var=cB)

    builtins_pred = PredicateBuiltins.ensure(mm.interner)
    wcel = mm.sym.label("wcel")
    mm.a(wcel, tc=wff, expr=[cA, builtins_pred.elem, cB])

    # Equality: class variables + wceq
    cA_eq = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="cA.wceq", kind="Var", origin_ref=0
    )
    cB_eq = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="cB.wceq", kind="Var", origin_ref=0
    )
    wceq_cA = mm.f(mm.sym.label("wceq.cA"), tc=wff, var=cA_eq)
    wceq_cB = mm.f(mm.sym.label("wceq.cB"), tc=wff, var=cB_eq)

    wceq = mm.sym.label("wceq")
    mm.a(wceq, tc=wff, expr=[cA_eq, builtins_pred.eq, cB_eq])

    # cv: class from setvar
    vx_cv = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.cv", kind="Var", origin_ref=0
    )
    wvx_cv = mm.f(mm.sym.label("vx.cv"), tc=wff, var=vx_cv)

    cv = mm.sym.label("cv")
    mm.a(cv, tc=wff, expr=[vx_cv])

    # wex: existential quantifier (wff)
    vx_wex = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.wex", kind="Var", origin_ref=0
    )
    wvx_wex = mm.f(mm.sym.label("vx.wex"), tc=wff, var=vx_wex)

    wex_label = mm.sym.label("wex")
    mm.a(wex_label, tc=wff, expr=[builtins_pred.exist, vx_wex, ph])
    # wal: universal quantifier (wff)
    vx_wal = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.wal", kind="Var", origin_ref=0
    )
    wvx_wal = mm.f(mm.sym.label("vx.wal"), tc=wff, var=vx_wal)

    wal_label = mm.sym.label("wal")
    mm.a(wal_label, tc=wff, expr=[builtins_pred.forall, vx_wal, ph])

    # ax-gen: generalization rule
    with mm.block():
        mm.e(mm.sym.label("ax-gen.1"), tc=provable, expr=[ph])
        mm.a(mm.sym.label("ax-gen"), tc=provable, expr=[builtins_pred.forall, vx_wal, ph])

    # ax-11: ∀ x ∀ y φ → ∀ y ∀ x φ
    vy_ax11 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax11", kind="Var", origin_ref=0
    )
    wvy_ax11 = mm.f(mm.sym.label("vy.ax11"), tc=wff, var=vy_ax11)

    ax_11_label = mm.sym.label("ax-11")
    mm.a(
        ax_11_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins_pred.forall,
            vx_wal,
            builtins_pred.forall,
            vy_ax11,
            ph,
            builtins.imp,
            builtins_pred.forall,
            vy_ax11,
            builtins_pred.forall,
            vx_wal,
            ph,
            builtins.rp,
        ],
    )

    # ax-10: ¬ ∀ x φ → ∀ x ¬ ∀ x φ
    ax_10_label = mm.sym.label("ax-10")
    mm.a(
        ax_10_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins.neg,
            builtins_pred.forall,
            vx_wal,
            ph,
            builtins.imp,
            builtins_pred.forall,
            vx_wal,
            builtins.neg,
            builtins_pred.forall,
            vx_wal,
            ph,
            builtins.rp,
        ],
    )

    # ax-4: ∀ x ( φ → ψ ) → ( ∀ x φ → ∀ x ψ )
    vx_ax4 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax4", kind="Var", origin_ref=0
    )
    wvx_ax4 = mm.f(mm.sym.label("vx.ax4"), tc=wff, var=vx_ax4)

    ax_4_label = mm.sym.label("ax-4")
    mm.a(
        ax_4_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins_pred.forall,
            vx_ax4,
            builtins.lp,
            ph,
            builtins.imp,
            ps,
            builtins.rp,
            builtins.imp,
            builtins.lp,
            builtins_pred.forall,
            vx_ax4,
            ph,
            builtins.imp,
            builtins_pred.forall,
            vx_ax4,
            ps,
            builtins.rp,
        ],
    )
    # ax-5: φ → ∀ x φ
    ax_5_label = mm.sym.label("ax-5")
    mm.a(
        ax_5_label,
        tc=provable,
        expr=[
            builtins.lp,
            ph,
            builtins.imp,
            builtins_pred.forall,
            vx_wal,
            ph,
            builtins.rp,
        ],
    )

    # ax-6: ¬ ∀ x ¬ x = y
    vx_ax6 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax6", kind="Var", origin_ref=0
    )
    wvx_ax6 = mm.f(mm.sym.label("vx.ax6"), tc=wff, var=vx_ax6)
    vy_ax6 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax6", kind="Var", origin_ref=0
    )
    wvy_ax6 = mm.f(mm.sym.label("vy.ax6"), tc=wff, var=vy_ax6)

    ax_6_label = mm.sym.label("ax-6")
    mm.a(
        ax_6_label,
        tc=provable,
        expr=[
            builtins.neg,
            builtins_pred.forall,
            vx_ax6,
            builtins.neg,
            vx_ax6,
            builtins_pred.eq,
            vy_ax6,
        ],
    )

    # ax-12: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    vx_ax12 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax12", kind="Var", origin_ref=0
    )
    wvx_ax12 = mm.f(mm.sym.label("vx.ax12"), tc=wff, var=vx_ax12)
    vy_ax12 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax12", kind="Var", origin_ref=0
    )
    wvy_ax12 = mm.f(mm.sym.label("vy.ax12"), tc=wff, var=vy_ax12)

    ax_12_label = mm.sym.label("ax-12")
    mm.a(
        ax_12_label,
        tc=provable,
        expr=[
            builtins.lp,
            vx_ax12,
            builtins_pred.eq,
            vy_ax12,
            builtins.imp,
            builtins.lp,
            builtins_pred.forall,
            vy_ax12,
            ph,
            builtins.imp,
            builtins_pred.forall,
            vx_ax12,
            builtins.lp,
            vx_ax12,
            builtins_pred.eq,
            vy_ax12,
            builtins.imp,
            ph,
            builtins.rp,
            builtins.rp,
            builtins.rp,
        ],
    )

    # ax-7: x = y → ( x = z → y = z )
    vx_ax7 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax7", kind="Var", origin_ref=0
    )
    wvx_ax7 = mm.f(mm.sym.label("vx.ax7"), tc=wff, var=vx_ax7)
    vy_ax7 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax7", kind="Var", origin_ref=0
    )
    wvy_ax7 = mm.f(mm.sym.label("vy.ax7"), tc=wff, var=vy_ax7)
    vz_ax7 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vz.ax7", kind="Var", origin_ref=0
    )
    wvz_ax7 = mm.f(mm.sym.label("vz.ax7"), tc=wff, var=vz_ax7)

    ax_7_label = mm.sym.label("ax-7")
    mm.a(
        ax_7_label,
        tc=provable,
        expr=[
            builtins.lp,
            vx_ax7,
            builtins_pred.eq,
            vy_ax7,
            builtins.imp,
            builtins.lp,
            vx_ax7,
            builtins_pred.eq,
            vz_ax7,
            builtins.imp,
            vy_ax7,
            builtins_pred.eq,
            vz_ax7,
            builtins.rp,
            builtins.rp,
        ],
    )

    # ax-8: x = y → ( x e. z → y e. z )
    vx_ax8 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax8", kind="Var", origin_ref=0
    )
    wvx_ax8 = mm.f(mm.sym.label("vx.ax8"), tc=wff, var=vx_ax8)
    vy_ax8 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax8", kind="Var", origin_ref=0
    )
    wvy_ax8 = mm.f(mm.sym.label("vy.ax8"), tc=wff, var=vy_ax8)
    vz_ax8 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vz.ax8", kind="Var", origin_ref=0
    )
    wvz_ax8 = mm.f(mm.sym.label("vz.ax8"), tc=wff, var=vz_ax8)

    ax_8_label = mm.sym.label("ax-8")
    mm.a(
        ax_8_label,
        tc=provable,
        expr=[
            builtins.lp,
            vx_ax8,
            builtins_pred.eq,
            vy_ax8,
            builtins.imp,
            builtins.lp,
            vx_ax8,
            builtins_pred.elem,
            vz_ax8,
            builtins.imp,
            vy_ax8,
            builtins_pred.elem,
            vz_ax8,
            builtins.rp,
            builtins.rp,
        ],
    )

    # ax-9: x = y → ( z e. x → z e. y )
    vx_ax9 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax9", kind="Var", origin_ref=0
    )
    wvx_ax9 = mm.f(mm.sym.label("vx.ax9"), tc=wff, var=vx_ax9)
    vy_ax9 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax9", kind="Var", origin_ref=0
    )
    wvy_ax9 = mm.f(mm.sym.label("vy.ax9"), tc=wff, var=vy_ax9)
    vz_ax9 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vz.ax9", kind="Var", origin_ref=0
    )
    wvz_ax9 = mm.f(mm.sym.label("vz.ax9"), tc=wff, var=vz_ax9)

    ax_9_label = mm.sym.label("ax-9")
    mm.a(
        ax_9_label,
        tc=provable,
        expr=[
            builtins.lp,
            vx_ax9,
            builtins_pred.eq,
            vy_ax9,
            builtins.imp,
            builtins.lp,
            vz_ax9,
            builtins_pred.elem,
            vx_ax9,
            builtins.imp,
            vz_ax9,
            builtins_pred.elem,
            vy_ax9,
            builtins.rp,
            builtins.rp,
        ],
    )
    # weu: there exists a unique (wff)
    vx_weu = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.weu", kind="Var", origin_ref=0
    )
    wvx_weu = mm.f(mm.sym.label("vx.weu"), tc=wff, var=vx_weu)

    weu_label = mm.sym.label("weu")
    mm.a(weu_label, tc=wff, expr=[builtins_pred.eu, vx_weu, ph])

    # wmo: there exists at most one (wff)
    vx_wmo = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.wmo", kind="Var", origin_ref=0
    )
    wvx_wmo = mm.f(mm.sym.label("vx.wmo"), tc=wff, var=vx_wmo)

    wmo_label = mm.sym.label("wmo")
    mm.a(wmo_label, tc=wff, expr=[builtins_pred.moeu, vx_wmo, ph])

    # wnf: not-free (wff)
    vx_wnf = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.wnf", kind="Var", origin_ref=0
    )
    wvx_wnf = mm.f(mm.sym.label("vx.wnf"), tc=wff, var=vx_wnf)

    wnf_label = mm.sym.label("wnf")
    mm.a(wnf_label, tc=wff, expr=[builtins_pred.nf, vx_wnf, ph])

    # wsb: proper substitution (wff)
    vy_wsb = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.wsb", kind="Var", origin_ref=0
    )
    wvy_wsb = mm.f(mm.sym.label("vy.wsb"), tc=wff, var=vy_wsb)
    vx_wsb = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.wsb", kind="Var", origin_ref=0
    )
    wvx_wsb = mm.f(mm.sym.label("vx.wsb"), tc=wff, var=vx_wsb)

    wsb_label = mm.sym.label("wsb")
    mm.a(
        wsb_label,
        tc=wff,
        expr=[builtins_pred.sb_lb, vy_wsb, builtins_pred.sb_slash, vx_wsb, builtins_pred.sb_rb, ph],
    )

    # df-ex: existential quantifier definition
    vx_dfex = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.dfex", kind="Var", origin_ref=0
    )
    wvx_dfex = mm.f(mm.sym.label("vx.dfex"), tc=wff, var=vx_dfex)

    df_ex_label = mm.sym.label("df-ex")
    mm.a(
        df_ex_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins_pred.exist,
            vx_dfex,
            ph,
            builtins.iff,
            builtins.neg,
            builtins_pred.forall,
            vx_dfex,
            builtins.neg,
            ph,
            builtins.rp,
        ],
    )

    # df-nf: not-free definition
    vx_dfnf = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.dfnf", kind="Var", origin_ref=0
    )
    wvx_dfnf = mm.f(mm.sym.label("vx.dfnf"), tc=wff, var=vx_dfnf)

    df_nf_label = mm.sym.label("df-nf")
    mm.a(
        df_nf_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins_pred.nf,
            vx_dfnf,
            ph,
            builtins.iff,
            builtins.lp,
            builtins_pred.exist,
            vx_dfnf,
            ph,
            builtins.imp,
            builtins_pred.forall,
            vx_dfnf,
            ph,
            builtins.rp,
            builtins.rp,
        ],
    )

    # df-mo: "exists at most one" definition
    vx_dfmo = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.dfmo", kind="Var", origin_ref=0
    )
    wvx_dfmo = mm.f(mm.sym.label("vx.dfmo"), tc=wff, var=vx_dfmo)

    vy_dfmo = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.dfmo", kind="Var", origin_ref=0
    )
    wvy_dfmo = mm.f(mm.sym.label("vy.dfmo"), tc=wff, var=vy_dfmo)

    df_mo_label = mm.sym.label("df-mo")
    mm.a(
        df_mo_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins_pred.moeu,
            vx_dfmo,
            ph,
            builtins.iff,
            builtins_pred.exist,
            vy_dfmo,
            builtins_pred.forall,
            vx_dfmo,
            builtins.lp,
            ph,
            builtins.imp,
            vx_dfmo,
            builtins_pred.eq,
            vy_dfmo,
            builtins.rp,
            builtins.rp,
        ],
    )

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
    # pure ¬→ Hilbert lowering path does not provide. The nullary top/bottom
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
            "wb": wb,
            "mp": ax_mp,
            "A1": ax_1,
            "A2": ax_2,
            "A3": ax_3,
        },
        floating_by_var=floating_by_var,
    )

    export_labels = [
        "cv",
        "wmo",
        "weu",
        "wex",
        "wal",
        "wa",
        "wcel",
        "wceq",
        "wo",
        "whad",
        "wif",
        "wxo",
        "wnf",
        "wsb",
        "wtru",
        "w3a",
        "w3o",
        "wnan",
        "wnor",
        "wcad",
        "wb",
        "wfal",
        "df-fal",
        "idi",
        "a1ii",
        "ax-1",
        "ax-2",
        "ax-3",
        "ax-4",
        "ax-mp",
        "ax-gen",
        "ax-5",
        "ax-6",
        "ax-10",
        "ax-11",
        "ax-12",
        "ax-7",
        "ax-8",
        "ax-9",
        "df-ex",
        "df-nf",
        "df-mo",
        *sorted(constructed.keys()),
    ]
    mm.export(
        wvx_wmo,
        wvx_weu,
        wvx_wex,
        wvx_wal,
        wvx_ax6,
        wvy_ax6,
        wvx_ax4,
        wvx_wnf,
        wvx_dfex,
        wvx_dfnf,
        wvx_dfmo,
        wvy_dfmo,
        wvx_cv,
        wcel_cA,
        wcel_cB,
        wceq_cA,
        wceq_cB,
        wvy_ax11,
        wvx_ax12,
        wvy_ax12,
        wvx_ax7,
        wvy_ax7,
        wvz_ax7,
        wvx_ax8,
        wvy_ax8,
        wvz_ax8,
        wvx_ax9,
        wvy_ax9,
        wvz_ax9,
        wvy_wsb,
        wvx_wsb,
        *(mm.sym.label(n) for n in export_labels),
    )
