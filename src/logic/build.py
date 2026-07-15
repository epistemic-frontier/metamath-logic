from __future__ import annotations

import logging
from collections.abc import Mapping
from dataclasses import dataclass

from skfd.api_v2 import BuildContextV2
from skfd.authoring.emit import emit_axioms, emit_lowered_lemmas
from skfd.authoring.formula import Wff
from skfd.authoring.parsing import wff as _parse_wff
from skfd.builder_v2 import MMBuilderV2
from skfd.core.symbols import SymbolId, SymbolInterner
from skfd.proof import Proof

from logic.predicate.hilbert import PredicateSystem
from logic.predicate.hilbert._builtins import PredicateBuiltins
from logic.predicate.hilbert.theorems import SETMM_TO_PREDICATE_THEOREMS
from logic.propositional.hilbert import System, _extend_names
from logic.propositional.hilbert._structures import Imp, phi, psi
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS

from .dv_contracts import ACTIVE_DV_PAIRS

_log = logging.getLogger(__name__)


def _active_dv_pairs(
    label: str, variables: Mapping[str, SymbolId]
) -> tuple[tuple[SymbolId, SymbolId], ...]:
    try:
        return tuple(
            (variables[left], variables[right]) for left, right in ACTIVE_DV_PAIRS.get(label, ())
        )
    except KeyError as exc:
        raise ValueError(f"{label}: no runtime variable for source DV endpoint {exc.args[0]!r}") from exc

@dataclass(frozen=True)
class _PredicateEmissionProvider:
    interner: SymbolInterner
    builtins: PredicateBuiltins
    statements: Mapping[str, Wff]

    def compile_axioms(self) -> Mapping[str, Wff]:
        return self.statements


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

    system = System.make(interner=mm.interner, names=_extend_names(ctx.names))
    builtins = system.builtins
    predicate_system = PredicateSystem.make(
        interner=mm.interner,
        names=system.names,
    )
    coverage = getattr(ctx, "coverage", None)
    if coverage is not None:
        coverage.declare_registry("propositional-hilbert", SETMM_TO_HILBERT_LEMMAS)
        coverage.declare_registry("predicate-hilbert", SETMM_TO_PREDICATE_THEOREMS)

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
        label_ids={"ax-1": ax_1, "ax-2": ax_2, "ax-3": ax_3},
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
    mm.a(wo, tc=wff, expr=[builtins.lp, ph, builtins.or_, ps, builtins.rp])
    mm.a(wa, tc=wff, expr=[builtins.lp, ph, builtins.and_, ps, builtins.rp])
    mm.a(wtru, tc=wff, expr=[builtins.tru])

    mm.a(wfal, tc=wff, expr=[builtins.fal])
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

    builtins_pred = predicate_system.builtins
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

    # cv: promote a setvar to a class.  Unlike the formula constructors above,
    # this syntax axiom has distinct Metamath typecodes and no expression token.
    setvar = mm.sym.const("setvar")
    class_ = mm.sym.const("class")
    vx_cv = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.cv", kind="Var", origin_ref=0
    )
    wvx_cv = mm.f(mm.sym.label("vx.cv"), tc=setvar, var=vx_cv)

    cv = mm.sym.label("cv")
    mm.a(cv, tc=class_, expr=[vx_cv])

    # weq: wff x = y
    vx_weq = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.weq", kind="Var", origin_ref=0
    )
    wvx_weq = mm.f(mm.sym.label("vx.weq"), tc=wff, var=vx_weq)
    vy_weq = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.weq", kind="Var", origin_ref=0
    )
    wvy_weq = mm.f(mm.sym.label("vy.weq"), tc=wff, var=vy_weq)

    weq_label = mm.sym.label("weq")
    mm.a(weq_label, tc=wff, expr=[vx_weq, builtins_pred.eq, vy_weq])

    # wel: membership wff specialized from class membership to set variables.
    wel_label = mm.sym.label("wel")
    wel_statement = Wff("wff", (vx_weq, builtins_pred.elem, vy_weq))
    mm.a(wel_label, tc=wff, expr=wel_statement.tokens)

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
            builtins.rp,
        ],
    )
    # ax-5: φ → ∀ x φ
    ax_5_label = mm.sym.label("ax-5")
    with mm.block():
        for left, right in _active_dv_pairs("ax-5", {"ph": ph, "x": vx_wal}):
            mm.d(left, right)
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
    # ax-13: ¬ x = y → ( y = z → ∀ x y = z )
    vx_ax13 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.ax13", kind="Var", origin_ref=0
    )
    wvx_ax13 = mm.f(mm.sym.label("vx.ax13"), tc=wff, var=vx_ax13)
    vy_ax13 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.ax13", kind="Var", origin_ref=0
    )
    wvy_ax13 = mm.f(mm.sym.label("vy.ax13"), tc=wff, var=vy_ax13)
    vz_ax13 = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vz.ax13", kind="Var", origin_ref=0
    )
    wvz_ax13 = mm.f(mm.sym.label("vz.ax13"), tc=wff, var=vz_ax13)

    ax_13_label = mm.sym.label("ax-13")
    mm.a(
        ax_13_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins.neg,
            vx_ax13,
            builtins_pred.eq,
            vy_ax13,
            builtins.imp,
            builtins.lp,
            vy_ax13,
            builtins_pred.eq,
            vz_ax13,
            builtins.imp,
            builtins_pred.forall,
            vx_ax13,
            vy_ax13,
            builtins_pred.eq,
            vz_ax13,
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
    vz_dfmo = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vz.dfmo", kind="Var", origin_ref=0
    )
    wvz_dfmo = mm.f(mm.sym.label("vz.dfmo"), tc=wff, var=vz_dfmo)

    df_mo_label = mm.sym.label("df-mo")
    df_mo_justification = (
        builtins.lp,
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
        builtins.iff,
        builtins_pred.exist,
        vz_dfmo,
        builtins_pred.forall,
        vx_dfmo,
        builtins.lp,
        ph,
        builtins.imp,
        vx_dfmo,
        builtins_pred.eq,
        vz_dfmo,
        builtins.rp,
        builtins.rp,
    )
    with mm.block():
        for left, right in _active_dv_pairs(
            "df-mo", {"ph": ph, "x": vx_dfmo, "y": vy_dfmo, "z": vz_dfmo}
        ):
            mm.d(left, right)
        mm.e(mm.sym.label("mojust.1"), tc=provable, expr=df_mo_justification)
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

    # df-eu: "there exists a unique" definition
    vx_dfeu = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.dfeu", kind="Var", origin_ref=0
    )
    wvx_dfeu = mm.f(mm.sym.label("vx.dfeu"), tc=wff, var=vx_dfeu)

    df_eu_label = mm.sym.label("df-eu")
    mm.a(
        df_eu_label,
        tc=provable,
        expr=[
            builtins.lp,
            builtins_pred.eu,
            vx_dfeu,
            ph,
            builtins.iff,
            builtins.lp,
            builtins_pred.exist,
            vx_dfeu,
            ph,
            builtins.and_,
            builtins_pred.moeu,
            vx_dfeu,
            ph,
            builtins.rp,
            builtins.rp,
        ],
    )

    # df-sb: proper substitution definition
    vt_dfsb = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vt.dfsb", kind="Var", origin_ref=0
    )
    wvt_dfsb = mm.f(mm.sym.label("vt.dfsb"), tc=wff, var=vt_dfsb)
    vx_dfsb = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vx.dfsb", kind="Var", origin_ref=0
    )
    wvx_dfsb = mm.f(mm.sym.label("vx.dfsb"), tc=wff, var=vx_dfsb)
    vy_dfsb = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vy.dfsb", kind="Var", origin_ref=0
    )
    wvy_dfsb = mm.f(mm.sym.label("vy.dfsb"), tc=wff, var=vy_dfsb)
    vz_dfsb = mm.interner.intern(
        origin_module_id=LOGIC_MODULE, local_name="vz.dfsb", kind="Var", origin_ref=0
    )
    wvz_dfsb = mm.f(mm.sym.label("vz.dfsb"), tc=wff, var=vz_dfsb)

    df_sb_label = mm.sym.label("df-sb")
    df_sb_expr = (
        builtins.lp,
        builtins_pred.sb_lb,
        vt_dfsb,
        builtins_pred.sb_slash,
        vx_dfsb,
        builtins_pred.sb_rb,
        ph,
        builtins.iff,
        builtins.lp,
        builtins_pred.forall,
        vy_dfsb,
        builtins.lp,
        vy_dfsb,
        builtins_pred.eq,
        vt_dfsb,
        builtins.imp,
        builtins_pred.forall,
        vx_dfsb,
        builtins.lp,
        vx_dfsb,
        builtins_pred.eq,
        vy_dfsb,
        builtins.imp,
        ph,
        builtins.rp,
        builtins.rp,
        builtins.and_,
        builtins_pred.forall,
        vz_dfsb,
        builtins.lp,
        vz_dfsb,
        builtins_pred.eq,
        vt_dfsb,
        builtins.imp,
        builtins_pred.forall,
        vx_dfsb,
        builtins.lp,
        vx_dfsb,
        builtins_pred.eq,
        vz_dfsb,
        builtins.imp,
        ph,
        builtins.rp,
        builtins.rp,
        builtins.rp,
        builtins.rp,
    )
    with mm.block():
        for left, right in _active_dv_pairs(
            "df-sb",
            {"ph": ph, "t": vt_dfsb, "x": vx_dfsb, "y": vy_dfsb, "z": vz_dfsb},
        ):
            mm.d(left, right)
        mm.a(
            df_sb_label,
            tc=provable,
            expr=df_sb_expr,
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
    # Tokens for which a proof has an emittable lowering path. The nullary
    # top/bottom constants T. / F. are emittable because they only appear as
    # opaque substitution targets during ref-unification.
    supported_tokens = {
        builtins.neg,
        builtins.imp,
        builtins.and_,
        builtins.iff,
        builtins.or_,
        builtins.nand,
        builtins.nor,
        builtins.xor,
        builtins.cadd,
        builtins.had,
        builtins.if_,
        builtins.tru,
        builtins.fal,
        builtins.lp,
        builtins.rp,
    }
    binary_tokens = {
        builtins.imp,
        builtins.and_,
        builtins.iff,
        builtins.or_,
        builtins.nand,
        builtins.nor,
        builtins.xor,
    }
    # Propositional variables that have a floating hypothesis in the prelude.
    floating_by_var = {
        prelude["ph"]: prelude["wph"],
        prelude["ps"]: prelude["wps"],
        prelude["ch"]: prelude["wch"],
        prelude["th"]: prelude["wth"],
        prelude["ta"]: prelude["wta"],
        prelude["et"]: prelude["wet"],
        prelude["ze"]: prelude["wze"],
        prelude["si"]: prelude["wsi"],
        prelude["rh"]: prelude["wrh"],
        prelude["mu"]: prelude["wmu"],
        prelude["la"]: prelude["wla"],
        prelude["ka"]: prelude["wka"],
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
        or a propositional variable with a floating hypothesis."""
        for st in getattr(p, "steps", ()):
            w = getattr(st, "wff", None)
            if w is None:
                continue
            operator_stack: list[list[SymbolId]] = []
            for t in w.tokens:
                if t in supported_tokens or t in floating_by_var:
                    if t == builtins.lp:
                        operator_stack.append([])
                    elif t == builtins.rp:
                        operators = operator_stack.pop()
                        if len(operators) > 2:
                            return False
                        if len(operators) == 2 and not (
                            operators[0] == operators[1]
                            and operators[0] in {builtins.and_, builtins.or_}
                        ):
                            return False
                    elif t in binary_tokens and operator_stack:
                        operator_stack[-1].append(t)
                else:
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
            "ax-1": ax_1,
            "ax-2": ax_2,
            "ax-3": ax_3,
        },
        floating_by_var=floating_by_var,
    )

    predicate_compiled_axioms = predicate_system.compile_axioms()
    predicate_foundations = {
        "ax-gen": Wff("wff", (builtins_pred.forall, vx_wal, ph)),
        "wel": wel_statement,
        "df-sb": Wff("wff", df_sb_expr),
        "df-ex": Wff(
            "wff",
            (
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
            ),
        ),
        "df-nf": Wff(
            "wff",
            (
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
            ),
        ),
        "df-eu": Wff(
            "wff",
            (
                builtins.lp,
                builtins_pred.eu,
                vx_dfeu,
                ph,
                builtins.iff,
                builtins.lp,
                builtins_pred.exist,
                vx_dfeu,
                ph,
                builtins.and_,
                builtins_pred.moeu,
                vx_dfeu,
                ph,
                builtins.rp,
                builtins.rp,
            ),
        ),
        "df-mo": Wff(
            "wff",
            (
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
            ),
        ),
        **{f"ax-{number}": compiled_axioms[f"ax-{number}"] for number in range(1, 4)},
        **{f"ax-{number}": predicate_compiled_axioms[f"ax-{number}"] for number in range(4, 14)},
    }
    predicate_constructed: dict[str, Proof] = {}
    predicate_excluded: dict[str, str] = {}
    for name, ctor in SETMM_TO_PREDICATE_THEOREMS.items():
        if name == "wel":
            continue
        if name in _DV_KNOWN_PROOF_DEFECTS:
            predicate_excluded[name] = (
                "pre-existing proof defect unrelated to DV closure: "
                f"{_DV_KNOWN_PROOF_DEFECTS[name]}"
            )
            continue
        try:
            predicate_constructed[name] = ctor(predicate_system)
        except Exception as exc:
            predicate_excluded[name] = f"construction failed: {exc}"

    predicate_base_refs = (
        set(compiled_axioms)
        | set(predicate_compiled_axioms)
        | set(predicate_foundations)
        | set(constructed)
    )
    changed = True
    while changed:
        changed = False
        for name in list(predicate_constructed):
            for ref in _refs(predicate_constructed[name]):
                if ref not in predicate_base_refs and ref not in predicate_constructed:
                    predicate_excluded[name] = f"depends on unavailable theorem {ref!r}"
                    del predicate_constructed[name]
                    changed = True
                    break

    if predicate_excluded:
        _log.info(
            "emitting %d/%d predicate theorems; excluded %d: %s",
            len(predicate_constructed),
            len(SETMM_TO_PREDICATE_THEOREMS),
            len(predicate_excluded),
            "; ".join(f"{n} ({r})" for n, r in sorted(predicate_excluded.items())),
        )

    predicate_floating_by_var: dict[SymbolId, SymbolId] = {}
    predicate_vars: set[SymbolId] = set()
    for proof in predicate_constructed.values():
        for step in proof.steps:
            predicate_vars.update(mm.auto.vars_in(step.wff.tokens))
    predicate_dv_names = {
        endpoint
        for label in predicate_constructed
        for pair in ACTIVE_DV_PAIRS.get(label, ())
        for endpoint in pair
    }
    predicate_vars.update(
        mm.interner.intern(
            origin_module_id="predicate", local_name=name, kind="Var", origin_ref=0
        )
        for name in predicate_dv_names
    )
    predicate_var_order = {
        name: index
        for index, name in enumerate(
            ("ph", "ps", "ch", "th", "ta", "et", "ze", "si", "rh", "mu", "la")
        )
    }
    for var in sorted(
        predicate_vars,
        key=lambda symbol: (
            predicate_var_order.get(mm.interner.symbol_table()[symbol].local_name, 100),
            symbol,
        ),
    ):
        local_name = mm.interner.symbol_table()[var].local_name
        predicate_floating_by_var[var] = mm.f(
            mm.sym.label(f"predicate.w{local_name}"),
            tc=wff,
            var=var,
        )
    predicate_vars_by_name = {
        mm.interner.symbol_table()[var].local_name: var for var in predicate_vars
    }
    predicate_active_dv = {
        label: _active_dv_pairs(label, predicate_vars_by_name)
        for label in predicate_constructed
        if label in ACTIVE_DV_PAIRS
    }

    predicate_provider = _PredicateEmissionProvider(
        interner=mm.interner,
        builtins=builtins_pred,
        statements={
            **compiled_axioms,
            **predicate_compiled_axioms,
            **predicate_foundations,
            **{name: proof.statement for name, proof in constructed.items()},
        },
    )

    # -- Bulk DV injection: source-extracted mandatory DV, restricted to
    # labels this run actually emits, resolved to this run's SymbolIds.
    # Labels that already carry a non-empty Proof.active_dv_pairs (e.g.
    # hand-authored via ProofBuilder.disjoint()) are left out of the table;
    # emit_lowered_lemmas requires side-table entries to match the Proof's
    # own pairs exactly rather than silently overriding them.
    import json as _json
    from pathlib import Path as _Path

    _dv_manifest_path = _Path(__file__).resolve().parents[2] / "dv_manifest.json"
    _dv_manifest: dict[str, list[list[str]]] = _json.loads(_dv_manifest_path.read_text())
    # Labels whose *existing* proof in this repo takes a different step
    # sequence than vanilla set.mm's derivation, so the DV scope literally
    # active at set.mm's assertion site is insufficient to replay this
    # repo's own proof. Source-vs-repo proof-path reconciliation is tracked
    # separately (see PR description); until then these are left exactly as
    # they were pre-DV-closure (no injected $d), which is a no-regression
    # baseline, not a silent contract weakening or strengthening.
    active_dv_pairs_by_label: dict[str, tuple[tuple[SymbolId, SymbolId], ...]] = {}
    for _name, _proof in predicate_constructed.items():
        if _proof.active_dv_pairs:
            continue
        _pairs: list[tuple[str, str]] = [
            (_v1, _v2) for _v1, _v2 in _dv_manifest.get(_name, [])
        ]
        _pairs.extend(_DV_EXTRA_ACTIVE_PAIRS.get(_name, ()))
        if not _pairs:
            continue
        active_dv_pairs_by_label[_name] = tuple(
            (_var(predicate_system, _v1), _var(predicate_system, _v2))
            for _v1, _v2 in _pairs
        )

    emit_lowered_lemmas(
        mm,
        predicate_provider,
        list(predicate_constructed.values()),
        typecode=provable,
        wff_typecode=wff,
        active_dv_pairs_by_label=active_dv_pairs_by_label,
        label_ids={
            "wi": prelude["wi"],
            "wn": prelude["wn"],
            "mp": ax_mp,
            "ax-1": ax_1,
            "ax-2": ax_2,
            "ax-3": ax_3,
            **{f"ax-{number}": mm.sym.label(f"ax-{number}") for number in range(4, 14)},
        },
        floating_by_var=predicate_floating_by_var,
        active_dv_pairs_by_label=predicate_active_dv,
        hypotheses_by_label={
            "ax-gen": (Wff("wff", (ph,)),),
            "df-mo": (Wff("wff", df_mo_justification),),
            **{
                name: tuple(step.wff for step in proof.steps if step.op == "hyp")
                for name, proof in constructed.items()
            },
        },
    )

    export_labels = [
        "cv",
        "weq",
        "wmo",
        "weu",
        "wex",
        "wal",
        "wa",
        "df-an",
        "df-nan",
        "wcel",
        "wel",
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
        "df-or",
        "df-bi",
        "df-xor",
        "df-had",
        "df-3or",
        "wnan",
        "wnor",
        "df-nor",
        "wcad",
        "df-cad",
        "df-ifp",
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
        "ax-13",
        "df-ex",
        "df-nf",
        "df-mo",
        "df-eu",
        "df-sb",
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
        wvx_dfeu,
        wvy_dfmo,
        wvz_dfmo,
        wvx_cv,
        wvx_weq,
        wvy_weq,
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
        wvx_ax13,
        wvy_ax13,
        wvz_ax13,
        wvy_wsb,
        wvx_wsb,
        wvt_dfsb,
        wvx_dfsb,
        wvy_dfsb,
        wvz_dfsb,
        *(mm.sym.label(n) for n in export_labels),
    )
